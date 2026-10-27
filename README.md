# Frame Scape

A Halo/Warframe-inspired first-person shooter that runs entirely in the browser. Plain static files: HTML, CSS and ES-module JavaScript. No build step, no server code, no binary assets (textures are generated on a canvas, sound is synthesized with WebAudio). Built to stay playable on very old hardware (Intel HD 3000 class) with an automatic quality ladder.

**Current state:** v0.8.2 plus the CH-06 (containers) patch and the CH-25.5 (drone damage) hotfix. The project is developed in AI-assisted patch sessions driven by a planner file (see below).

## Run it

ES modules do not load from `file://`, so serve the folder over HTTP:

```bash
python -m http.server 8000
```

Then open <http://localhost:8000/> for the overview page, or <http://localhost:8000/frame-scape/> to play directly.

The only external dependency is three.js r152.2, loaded from jsDelivr through the import map in `frame-scape/index.html`. See `docs/GAME_REFERENCE.md` for the optional fully-offline setup.

## Repository layout

```
.
├── README.md                this file
├── index.html               overview page (links to the game)
├── framescape.flat.txt      the planner / AI handoff file (read this first if you are an AI)
├── AGENTS.md                short instructions for AI coding assistants
├── docs/
│   └── GAME_REFERENCE.md    detailed reference: controls, mods, economy, performance, changelog
└── frame-scape/             the game itself (what you deploy)
    ├── index.html           entry point, HUD skeleton, import map
    ├── css/hud.css          HUD and menu styling
    └── js/
        ├── assets.js        ALL tunable config: palette, world, weapons, enemies, drops, mods
        ├── main.js          boot, game loop, zones, day/night, respawns, save state, watchdog
        ├── world.js         corridor, hangar, valley, city and procedural wilderness builder
        ├── player.js        FPS physics, shield/health, energy, cloak, knockdown
        ├── weapon.js        guns, melee, typed damage (typedHit), selling
        ├── enemy.js         enemy archetypes, elite ability kits, hounds, kaiju
        ├── specials.js      R2 special slots, ordnance, mod chips, pickups
        ├── companions.js    combat drone and cursor-led beast
        ├── ecology.js       birds, rodents, fish, fishing, harvesting
        ├── mods.js          credits and power bank, mod cards, drop curve
        ├── hud.js           HUD, radar, day/night clock, pause menu (XMB)
        ├── input.js         keyboard, mouse (pointer lock) and Xbox gamepad
        ├── textures.js      procedural canvas textures
        └── audio.js         WebAudio-synthesized sound effects
```

Design rule used throughout: gameplay numbers live in `frame-scape/js/assets.js`, not hard-coded in logic files.

## How development works

All work is planned in `framescape.flat.txt`, a flat `key = value` file:

- feature requests are logged as feature lines and grouped into dependency-ordered **chunks** (CH-01 and up), each sized to fit one AI session
- one patch session = finish one chunk, then deliver **both** the updated game and the updated planner file
- `meta.plan.next` names the next chunk to run (currently CH-07, hangar bay expansion)
- `worklog.*` entries are the patch history; code changes carry `/* CH-NN.X */` markers

## For AI assistants

1. Read `AGENTS.md`, then the header of `framescape.flat.txt` (the protocol sections 01 and 02 and the project profile in section 03).
2. Find the chunk named by `meta.plan.next` and read its whole block.
3. Make the changes in `frame-scape/`, update the planner file as the protocol describes, and leave `/* CH-NN.X */` markers in the code.

## Controls (short version)

WASD move, mouse look, left click fire, E/G special item, Q swap weapon, R reload, Space jump (again for double jump), Esc/P menu, F3 FPS readout. Xbox controllers are supported. Full table in `docs/GAME_REFERENCE.md`.

## Legal

Fan homage for personal and educational use. Halo and Warframe are trademarks of their respective owners. No game assets, names or sounds from those games are included. Keep it non-commercial.
