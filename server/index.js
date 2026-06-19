const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });

app.use(express.static(path.join(__dirname, 'public')));

// ─── Game Constants ───────────────────────────────────────────────
const TICK_RATE = 60;
const TICK_MS = 1000 / TICK_RATE;

// Physics
const RAMP_LENGTH = 80;          // metres equivalent
const RAMP_ANGLE = 11;           // degrees from horizontal at takeoff
const GRAVITY = 9.8;             // m/s²
const MAX_SPEED = 28;            // m/s at full charge
const MIN_SPEED = 18;
const CHARGE_TIME = 2.5;         // seconds to full charge
const JUMP_WINDOW = 0.4;         // seconds near ramp end for optimal launch
const FLIGHT_SCALE = 0.06;       // canvas pixels per metre (handled client-side)

// Scoring
const DISTANCE_PER_POINT = 1;
const MAX_POSTURE_BONUS = 30;
const PERFECT_LANDING_BONUS = 20;
const FALL_DISTANCE_MULT = 0.7;
const PERFECT_LANDING_WINDOW = 0.25; // seconds before touchdown

const ROUNDS = 3;

// ─── Phase Enum ───────────────────────────────────────────────────
const Phase = {
  WAITING: 'waiting',
  COUNTDOWN: 'countdown',
  RUNUP: 'runup',
  FLIGHT: 'flight',
  LANDED: 'landed',
  ROUND_END: 'round_end',
  GAME_OVER: 'game_over',
};

// ─── Rooms ────────────────────────────────────────────────────────
const rooms = new Map();
let waitingRoom = null;

function createRoom(id) {
  return {
    id,
    players: [],          // [socket, socket]
    phase: Phase.WAITING,
    round: 0,
    scores: [[], []],     // per-round best scores
    jumpScores: [0, 0],   // current jump scores
    state: [null, null],  // player physics state
    readyFlags: [false, false],
    landedFlags: [false, false],
    countdownTimer: null,
    gameLoop: null,
  };
}

function initPlayerState(slotIndex) {
  return {
    slot: slotIndex,
    phase: Phase.RUNUP,
    chargeTime: 0,
    speed: 0,
    launched: false,
    launchSpeed: 0,
    launchAngle: 0,
    x: 0,           // metres from takeoff point
    y: 0,           // metres above landing slope
    vx: 0,
    vy: 0,
    airTime: 0,
    postureTime: 0,
    landed: false,
    fell: false,
    distance: 0,
    postureBonus: 0,
    landingBonus: 0,
    score: 0,
    holdActive: false,
    // for landing detection
    timeToLanding: null,
    landingCountdown: null,
  };
}

// Simple landing slope: y = -tan(35°) * x  (slope going down)
const SLOPE_ANGLE_RAD = 35 * Math.PI / 180;
const SLOPE_K = Math.tan(SLOPE_ANGLE_RAD); // y_slope = -k * x

function slopeY(x) {
  // positive x = forward, returns the slope height (starts at 0, goes negative)
  return -SLOPE_K * x;
}

function tickPlayer(ps, dt) {
  if (ps.landed) return;

  if (ps.phase === Phase.RUNUP) {
    if (ps.holdActive) {
      ps.chargeTime += dt;
      if (ps.chargeTime >= CHARGE_TIME) {
        ps.chargeTime = CHARGE_TIME;
        // Auto-launch at max charge
        triggerLaunch(ps, true);
      }
    }
    ps.speed = MIN_SPEED + (MAX_SPEED - MIN_SPEED) * (ps.chargeTime / CHARGE_TIME);
  }

  if (ps.phase === Phase.FLIGHT) {
    ps.vx += 0;          // no drag for simplicity
    ps.vy -= GRAVITY * dt;

    // Posture bonus accumulation
    if (ps.holdActive) {
      ps.postureTime += dt;
    }

    ps.x += ps.vx * dt;
    ps.y += ps.vy * dt;
    ps.airTime += dt;

    // Landing: check if player hits slope
    const sy = slopeY(ps.x);
    if (ps.x > 0.5 && ps.y <= sy) {
      // Landed
      ps.distance = Math.max(0, ps.x);
      ps.phase = Phase.LANDED;
      ps.landed = true;

      // Posture bonus
      ps.postureBonus = Math.min(MAX_POSTURE_BONUS,
        Math.round((ps.postureTime / Math.max(ps.airTime, 0.01)) * MAX_POSTURE_BONUS));

      // Landing bonus: player released hold within PERFECT_LANDING_WINDOW before landing
      const timeSinceRelease = ps.landingReleaseAt != null ? (ps.airTime - ps.landingReleaseAt) : 999;
      const perfectLanding = (!ps.holdActive) && timeSinceRelease >= 0 && timeSinceRelease <= PERFECT_LANDING_WINDOW;
      ps.landingBonus = perfectLanding ? PERFECT_LANDING_BONUS : 0;

      // Fell: if vertical velocity is too steep (bad form)
      const landingAngle = Math.abs(Math.atan2(-ps.vy, ps.vx) * 180 / Math.PI);
      ps.fell = landingAngle > 75;

      let rawScore = ps.distance * DISTANCE_PER_POINT + ps.postureBonus + ps.landingBonus;
      if (ps.fell) rawScore *= FALL_DISTANCE_MULT;
      ps.score = Math.round(rawScore);
    }
  }
}

function triggerLaunch(ps, auto = false) {
  if (ps.launched) return;
  ps.launched = true;
  ps.phase = Phase.FLIGHT;

  // Angle: optimal is RAMP_ANGLE. If auto (max charge), give full angle.
  // If manual release, angle depends on chargeTime proportion
  const chargeRatio = ps.chargeTime / CHARGE_TIME;
  ps.launchSpeed = MIN_SPEED + (MAX_SPEED - MIN_SPEED) * chargeRatio;

  // Best angle is at chargeRatio ~ 0.85-1.0
  const angleDeg = RAMP_ANGLE * Math.min(1, chargeRatio / 0.85);
  ps.launchAngle = angleDeg * Math.PI / 180;

  ps.vx = ps.launchSpeed * Math.cos(ps.launchAngle);
  ps.vy = ps.launchSpeed * Math.sin(ps.launchAngle);
  ps.x = 0;
  ps.y = 0;
  ps.airTime = 0;
  ps.postureTime = 0;
}

function handleInput(room, slotIndex, hold) {
  const ps = room.state[slotIndex];
  if (!ps || ps.landed) return;

  const wasHeld = ps.holdActive;
  ps.holdActive = hold;

  if (ps.phase === Phase.RUNUP) {
    // Release during runup = launch
    if (wasHeld && !hold) {
      triggerLaunch(ps, false);
    }
  }

  if (ps.phase === Phase.FLIGHT) {
    // Release in flight = mark landing release time
    if (wasHeld && !hold) {
      ps.landingReleaseAt = ps.airTime;
    }
  }
}

function computeRoundScores(room) {
  for (let i = 0; i < 2; i++) {
    const ps = room.state[i];
    if (ps) {
      const prev = room.scores[i][room.round - 1] || 0;
      room.scores[i][room.round - 1] = Math.max(prev, ps.score);
    }
  }
}

function bestScore(room, slotIndex) {
  return Math.max(0, ...room.scores[slotIndex]);
}

function startRound(room) {
  room.round++;
  room.landedFlags = [false, false];
  room.state = [initPlayerState(0), initPlayerState(1)];
  room.phase = Phase.RUNUP;

  broadcast(room, 'round_start', { round: room.round, totalRounds: ROUNDS });

  room.gameLoop = setInterval(() => gameTick(room), TICK_MS);
}

function gameTick(room) {
  const dt = TICK_MS / 1000;
  for (let i = 0; i < 2; i++) {
    const ps = room.state[i];
    if (ps) tickPlayer(ps, dt);
  }

  // Check if both landed
  const bothLanded = room.state.every(ps => ps && ps.landed);
  if (bothLanded && room.phase !== Phase.ROUND_END) {
    room.phase = Phase.ROUND_END;
    clearInterval(room.gameLoop);
    computeRoundScores(room);

    const payload = {
      round: room.round,
      scores: room.state.map(ps => ({
        distance: ps.distance.toFixed(1),
        postureBonus: ps.postureBonus,
        landingBonus: ps.landingBonus,
        fell: ps.fell,
        score: ps.score,
      })),
      totals: [bestScore(room, 0), bestScore(room, 1)],
    };
    broadcast(room, 'round_end', payload);

    if (room.round >= ROUNDS) {
      setTimeout(() => endGame(room), 3000);
    } else {
      setTimeout(() => startRound(room), 4000);
    }
  }

  // Broadcast state every tick
  broadcast(room, 'game_state', {
    players: room.state.map(ps => ps ? {
      phase: ps.phase,
      chargeTime: ps.chargeTime,
      chargeMax: CHARGE_TIME,
      x: ps.x,
      y: ps.y,
      vx: ps.vx,
      vy: ps.vy,
      launched: ps.launched,
      landed: ps.landed,
      fell: ps.fell,
      holdActive: ps.holdActive,
      postureTime: ps.postureTime,
      airTime: ps.airTime,
      score: ps.score,
    } : null),
  });
}

function endGame(room) {
  room.phase = Phase.GAME_OVER;
  const s0 = bestScore(room, 0);
  const s1 = bestScore(room, 1);
  const winner = s0 > s1 ? 0 : s1 > s0 ? 1 : -1; // -1 = tie
  broadcast(room, 'game_over', { scores: [s0, s1], winner });
}

function broadcast(room, event, data) {
  for (const sock of room.players) {
    sock.emit(event, data);
  }
}

// ─── Socket Handling ──────────────────────────────────────────────
io.on('connection', (socket) => {
  let myRoom = null;
  let mySlot = -1;

  // Matchmaking
  if (waitingRoom && waitingRoom.players.length === 1) {
    myRoom = waitingRoom;
    waitingRoom = null;
  } else {
    myRoom = createRoom(`room_${Date.now()}`);
    rooms.set(myRoom.id, myRoom);
    waitingRoom = myRoom;
  }

  mySlot = myRoom.players.length;
  myRoom.players.push(socket);

  socket.emit('joined', { slot: mySlot, roomId: myRoom.id });

  if (myRoom.players.length === 2) {
    broadcast(myRoom, 'opponent_joined', {});
    // Countdown
    let count = 3;
    broadcast(myRoom, 'countdown', { count });
    const cd = setInterval(() => {
      count--;
      if (count > 0) {
        broadcast(myRoom, 'countdown', { count });
      } else {
        clearInterval(cd);
        startRound(myRoom);
      }
    }, 1000);
  }

  socket.on('input', ({ hold }) => {
    if (myRoom && mySlot >= 0) {
      handleInput(myRoom, mySlot, !!hold);
    }
  });

  socket.on('disconnect', () => {
    if (myRoom) {
      broadcast(myRoom, 'opponent_left', {});
      clearInterval(myRoom.gameLoop);
      rooms.delete(myRoom.id);
      if (waitingRoom === myRoom) waitingRoom = null;
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Ski Jump server on :${PORT}`));
