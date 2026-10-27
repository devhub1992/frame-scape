# Instructions for AI coding assistants

This repo is a static browser game (no build step, ES modules, three.js from CDN).

1. Start with `frame-scape-patched/framescape.flat.txt`. It is the single source of truth for what to build next and how to record it. Read its header comments, the `ai.*` protocol keys, the chunk named in `meta.plan.next`, and the project profile.
2. Work on ONE chunk per session and finish all of its open features.
3. The game lives in `frame-scape/`. Tunable numbers belong in `frame-scape/js/assets.js`.
4. When done, deliver the updated game folder and the updated `framescape.flat.txt` (flip statuses, update `meta.last-patch` and `meta.plan.next`, append a `worklog.*` entry). Mark code changes with `/* CH-NN.X */` comments.
5. To test, serve the repo root with `python -m http.server 8000`; `file://` will not work because of ES modules.
6. `docs/GAME_REFERENCE.md` holds detailed controls, mod/economy tables and performance notes. Its folder tree is outdated (it says `halo-shooter/`; the real folder is `frame-scape/`).
