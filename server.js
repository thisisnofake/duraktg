const path = require('path');
const http = require('http');
const express = require('express');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });

app.use(express.static(path.join(__dirname, 'public')));

const rooms = {}; // roomId -> room
const SUITS = ['H', 'D', 'C', 'S'];

/* ---------- Utils ---------- */
function genRoomId() {
  let id;
  do { id = String(Math.floor(1000 + Math.random() * 9000)); } while (rooms[id]);
  return id;
}

function createDeck(size) {
  const minRank = size === 24 ? 9 : size === 36 ? 6 : 2;
  const deck = [];
  for (const s of SUITS) for (let r = minRank; r <= 14; r++) deck.push({ r, s });
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

function findCard(hand, c) {
  return hand.find(x => x.r === c.r && x.s === c.s);
}

function canBeat(card, against, trump) {
  if (card.s === against.s) return card.r > against.r;
  return card.s === trump;
}

/* ---------- Game logic ---------- */
function startGame(room) {
  const { deckSize } = room.config;
  const deck = createDeck(deckSize);

  const hands = {};
  for (const p of room.players) hands[p.id] = deck.splice(0, 6);

  let trumpCard = deck.length > 0 ? deck[deck.length - 1] : null;
  let trump;
  if (trumpCard) trump = trumpCard.s;
  else {
    const last = room.players[room.players.length - 1];
    const lastCard = hands[last.id][hands[last.id].length - 1];
    trump = lastCard ? lastCard.s : 'S';
    trumpCard = lastCard;
  }

  // First attacker = player with lowest trump
  let firstAtk = room.players[0].id;
  let lowest = 99;
  for (const p of room.players) {
    for (const c of hands[p.id]) {
      if (c.s === trump && c.r < lowest) { lowest = c.r; firstAtk = p.id; }
    }
  }

  const order = room.players.map(p => p.id);
  const atkIdx = order.indexOf(firstAtk);
  const defender = order[(atkIdx + 1) % order.length];

  room.game = {
    deck, trump, trumpCard, hands,
    table: [],           // [{atk, def|null}]
    discard: [],
    attacker: firstAtk,
    defender,
    passed: new Set(),
    finished: [],
    order,
    currentCycleIdx: atkIdx,
    status: 'playing',
    durak: null
  };

  broadcastState(room);
}

function findNextThrower(room, fromIdx) {
  const game = room.game;
  for (let i = 1; i <= game.order.length; i++) {
    const idx = (fromIdx + i) % game.order.length;
    const id = game.order[idx];
    if (id === game.defender) continue;
    if (game.finished.includes(id)) continue;
    if (game.passed.has(id)) continue;
    return { idx, id };
  }
  return null;
}

function currentActorId(room) {
  const game = room.game;
  if (game.status !== 'playing') return null;
  const hasUnbeaten = game.table.some(p => p.def === null);
  if (hasUnbeaten) return game.defender;
  if (game.table.length === 0) return game.attacker;
  return game.order[game.currentCycleIdx];
}

function drawUpTo(room, playerId) {
  const game = room.game;
  const hand = game.hands[playerId];
  const needed = Math.max(0, 6 - hand.length);
  for (let i = 0; i < needed && game.deck.length > 0; i++) {
    hand.push(game.deck.shift());
  }
}

function endBout(room, defenderTook) {
  const game = room.game;
  const oldAttacker = game.attacker;
  const oldDefender = game.defender;

  if (defenderTook) {
    for (const pair of game.table) {
      game.hands[oldDefender].push(pair.atk);
      if (pair.def) game.hands[oldDefender].push(pair.def);
    }
  } else {
    for (const pair of game.table) {
      game.discard.push(pair.atk);
      if (pair.def) game.discard.push(pair.def);
    }
  }

  // Draw order: old attacker first, then clockwise (defender last)
  const drawOrder = [];
  const drawStartIdx = game.order.indexOf(oldAttacker);
  for (let i = 0; i < game.order.length; i++) {
    const id = game.order[(drawStartIdx + i) % game.order.length];
    if (id === oldDefender) continue;
    drawOrder.push(id);
  }
  drawOrder.push(oldDefender);
  for (const id of drawOrder) {
    if (!game.finished.includes(id)) drawUpTo(room, id);
  }

  // Mark finished
  for (const id of game.order) {
    if (!game.finished.includes(id) && game.hands[id].length === 0 && game.deck.length === 0) {
      game.finished.push(id);
    }
  }

  // Check game over
  const active = game.order.filter(id => !game.finished.includes(id));
  if (active.length <= 1) {
    game.status = 'finished';
    game.durak = active[0] || null;
    return;
  }

  // Pick new attacker
  let startIdx;
  if (defenderTook) {
    startIdx = (game.order.indexOf(oldDefender) + 1) % game.order.length;
  } else {
    startIdx = game.order.indexOf(oldDefender);
  }
  for (let i = 0; i < game.order.length; i++) {
    const id = game.order[(startIdx + i) % game.order.length];
    if (!game.finished.includes(id)) { game.attacker = id; break; }
  }
  // Pick new defender
  const atkIdx = game.order.indexOf(game.attacker);
  for (let i = 1; i <= game.order.length; i++) {
    const id = game.order[(atkIdx + i) % game.order.length];
    if (!game.finished.includes(id)) { game.defender = id; break; }
  }

  game.table = [];
  game.passed.clear();
  game.currentCycleIdx = game.order.indexOf(game.attacker);
}

/* ---------- Action handlers ---------- */
function err(msg) { return { error: msg }; }

function handleAttack(room, playerId, card) {
  const game = room.game;
  if (!game || game.status !== 'playing') return err('Игра окончена');
  if (!card || typeof card.r !== 'number' || !SUITS.includes(card.s)) return err('Некорректная карта');

  const hasUnbeaten = game.table.some(p => p.def === null);
  if (hasUnbeaten) return err('Сначала отбейся');

  if (game.table.length === 0) {
    if (playerId !== game.attacker) return err('Не твой ход');
  } else {
    const actorId = game.order[game.currentCycleIdx];
    if (actorId !== playerId) return err('Не твой ход');
    if (game.passed.has(playerId)) return err('Ты уже спассовал');
    if (playerId === game.defender) return err('Защитник не подкидывает');
  }

  const hand = game.hands[playerId];
  const c = findCard(hand, card);
  if (!c) return err('Карты нет в руке');

  if (game.table.length >= 6) return err('Максимум 6 карт в кону');

  // Rank must match any card on table (for throw-in)
  if (game.table.length > 0) {
    const ranks = new Set();
    for (const pair of game.table) {
      ranks.add(pair.atk.r);
      if (pair.def) ranks.add(pair.def.r);
    }
    if (!ranks.has(c.r)) return err('Нужен ранг с карт на столе');
  }

  hand.splice(hand.indexOf(c), 1);
  game.table.push({ atk: c, def: null });
  return { ok: true };
}

function handleDefend(room, playerId, card) {
  const game = room.game;
  if (!game || game.status !== 'playing') return err('Игра окончена');
  if (playerId !== game.defender) return err('Ты не защищаешься');

  const unbeaten = game.table.find(p => p.def === null);
  if (!unbeaten) return err('Нечего отбивать');

  const hand = game.hands[playerId];
  const c = findCard(hand, card);
  if (!c) return err('Карты нет в руке');
  if (!canBeat(c, unbeaten.atk, game.trump)) return err('Не бьёт');

  hand.splice(hand.indexOf(c), 1);
  unbeaten.def = c;

  const stillUnbeaten = game.table.some(p => p.def === null);
  if (!stillUnbeaten) {
    const next = findNextThrower(room, game.currentCycleIdx);
    if (next) game.currentCycleIdx = next.idx;
    else endBout(room, false);
  }
  return { ok: true };
}

function handleTake(room, playerId) {
  const game = room.game;
  if (!game || game.status !== 'playing') return err('Игра окончена');
  if (playerId !== game.defender) return err('Ты не защищаешься');
  const hasUnbeaten = game.table.some(p => p.def === null);
  if (!hasUnbeaten) return err('Нет неотбитых карт');
  endBout(room, true);
  return { ok: true };
}

function handlePass(room, playerId) {
  const game = room.game;
  if (!game || game.status !== 'playing') return err('Игра окончена');
  const hasUnbeaten = game.table.some(p => p.def === null);
  if (hasUnbeaten) return err('Нужно отбиваться или взять');
  if (game.table.length === 0) return err('Нужно атаковать');
  if (playerId === game.defender) return err('Защитник не пасует');

  const actorId = game.order[game.currentCycleIdx];
  if (actorId !== playerId) return err('Не твой ход');

  game.passed.add(playerId);
  const next = findNextThrower(room, game.currentCycleIdx);
  if (next) game.currentCycleIdx = next.idx;
  else endBout(room, false);
  return { ok: true };
}

/* ---------- State broadcast ---------- */
function computeCanAct(room, playerId) {
  const game = room.game;
  const no = { attack: false, defend: false, pass: false, take: false };
  if (!game || game.status !== 'playing') return no;
  const actor = currentActorId(room);
  if (actor !== playerId) return no;
  const hasUnbeaten = game.table.some(p => p.def === null);
  if (hasUnbeaten) {
    return { attack: false, defend: playerId === game.defender, pass: false, take: playerId === game.defender };
  }
  const hand = game.hands[playerId];
  const ranks = new Set();
  for (const pair of game.table) { ranks.add(pair.atk.r); if (pair.def) ranks.add(pair.def.r); }
  const canThrow = game.table.length < 6 && hand.some(c => ranks.size === 0 || ranks.has(c.r));
  return {
    attack: game.table.length === 0 ? playerId === game.attacker : canThrow,
    defend: false,
    pass: game.table.length > 0,
    take: false
  };
}

function buildPlayerState(room, playerId) {
  const g = room.game;
  return {
    players: room.players.map(p => ({
      id: p.id,
      name: p.name,
      handCount: g.hands[p.id].length,
      finished: g.finished.includes(p.id)
    })),
    myHand: g.hands[playerId].slice(),
    table: g.table.map(pair => ({ atk: pair.atk, def: pair.def })),
    deckCount: g.deck.length,
    trump: g.trump,
    trumpCard: g.trumpCard,
    attacker: g.attacker,
    defender: g.defender,
    currentActor: currentActorId(room),
    status: g.status,
    durakId: g.durak,
    canAct: computeCanAct(room, playerId)
  };
}

function broadcastState(room) {
  if (!room.game) return;
  for (const p of room.players) {
    io.to(p.id).emit('game:state', buildPlayerState(room, p.id));
  }
  if (room.game.status === 'finished') {
    const durak = room.players.find(p => p.id === room.game.durak);
    io.to(room.id).emit('game:over', {
      durakId: room.game.durak,
      durakName: durak ? durak.name : null
    });
  }
}

function broadcastRoom(room) {
  const payload = {
    id: room.id,
    hostId: room.hostId,
    players: room.players.map(p => ({ id: p.id, name: p.name })),
    config: room.config
  };
  io.to(room.id).emit('room:update', payload);
}

/* ---------- Socket wiring ---------- */
io.on('connection', (socket) => {
  socket.on('room:create', ({ name, maxPlayers, deckSize }, cb) => {
    const n = String(name || '').trim().slice(0, 16) || 'Игрок';
    maxPlayers = [2, 3, 4].includes(+maxPlayers) ? +maxPlayers : 2;
    deckSize = [24, 36, 52].includes(+deckSize) ? +deckSize : 36;
    if (deckSize < maxPlayers * 6) return cb({ error: 'Колода слишком мала для такого числа игроков' });

    const id = genRoomId();
    const room = {
      id,
      hostId: socket.id,
      players: [{ id: socket.id, name: n }],
      config: { maxPlayers, deckSize },
      game: null
    };
    rooms[id] = room;
    socket.data.roomId = id;
    socket.join(id);
    cb({ ok: true, roomId: id, youId: socket.id });
    broadcastRoom(room);
  });

  socket.on('room:join', ({ roomId, name }, cb) => {
    const room = rooms[String(roomId || '').trim()];
    if (!room) return cb({ error: 'Комната не найдена' });
    if (room.players.length >= room.config.maxPlayers) return cb({ error: 'Комната заполнена' });
    if (room.game) return cb({ error: 'Игра уже началась' });

    const n = String(name || '').trim().slice(0, 16) || 'Игрок';
    room.players.push({ id: socket.id, name: n });
    socket.data.roomId = room.id;
    socket.join(room.id);
    cb({ ok: true, roomId: room.id, youId: socket.id });
    broadcastRoom(room);
  });

  socket.on('room:leave', () => {
    const rid = socket.data.roomId;
    if (!rid || !rooms[rid]) return;
    const room = rooms[rid];
    room.players = room.players.filter(p => p.id !== socket.id);
    socket.leave(rid);
    socket.data.roomId = null;
    if (room.players.length === 0) delete rooms[rid];
    else {
      if (room.hostId === socket.id) room.hostId = room.players[0].id;
      if (room.game) {
        io.to(rid).emit('game:over', { durakId: null, durakName: null, reason: 'Игрок вышел' });
        room.game = null;
      }
      broadcastRoom(room);
    }
  });

  socket.on('game:start', (cb) => {
    const rid = socket.data.roomId;
    const room = rid && rooms[rid];
    if (!room) return cb && cb({ error: 'Нет комнаты' });
    if (room.hostId !== socket.id) return cb && cb({ error: 'Только хост может начать' });
    if (room.players.length < 2) return cb && cb({ error: 'Нужно минимум 2 игрока' });
    if (room.game) return cb && cb({ error: 'Игра уже идёт' });
    startGame(room);
    cb && cb({ ok: true });
  });

  socket.on('game:attack', (data, cb) => {
    const rid = socket.data.roomId;
    const room = rid && rooms[rid];
    if (!room || !room.game) return cb({ error: 'Нет активной игры' });
    const res = handleAttack(room, socket.id, data && data.card);
    if (res.error) return cb(res);
    broadcastState(room);
    cb({ ok: true });
  });

  socket.on('game:defend', (data, cb) => {
    const rid = socket.data.roomId;
    const room = rid && rooms[rid];
    if (!room || !room.game) return cb({ error: 'Нет активной игры' });
    const res = handleDefend(room, socket.id, data && data.card);
    if (res.error) return cb(res);
    broadcastState(room);
    cb({ ok: true });
  });

  socket.on('game:take', (cb) => {
    const rid = socket.data.roomId;
    const room = rid && rooms[rid];
    if (!room || !room.game) return cb({ error: 'Нет активной игры' });
    const res = handleTake(room, socket.id);
    if (res.error) return cb(res);
    broadcastState(room);
    cb({ ok: true });
  });

  socket.on('game:pass', (cb) => {
    const rid = socket.data.roomId;
    const room = rid && rooms[rid];
    if (!room || !room.game) return cb({ error: 'Нет активной игры' });
    const res = handlePass(room, socket.id);
    if (res.error) return cb(res);
    broadcastState(room);
    cb({ ok: true });
  });

  socket.on('disconnect', () => {
    const rid = socket.data.roomId;
    if (!rid || !rooms[rid]) return;
    const room = rooms[rid];
    room.players = room.players.filter(p => p.id !== socket.id);
    if (room.players.length === 0) {
      delete rooms[rid];
    } else {
      if (room.hostId === socket.id) room.hostId = room.players[0].id;
      if (room.game) {
        io.to(rid).emit('game:over', { durakId: null, durakName: null, reason: 'Игрок отключился' });
        room.game = null;
      }
      broadcastRoom(room);
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Durak server on :' + PORT));
