# HOLPY Frontend (Vue 3)

Vue 3 + Vite single-page app for holpy. Talks to the Flask backend in
`../backend/` through `/api/*` (dev proxy target `http://127.0.0.1:5000`,
see `vite.config.js`).

## Setup

```bash
npm install
```

## Development

```bash
npm run dev          # http://localhost:8080
```

## Build

```bash
npm run build        # output in dist/
```

## Routes

- `/` — `views/Index.vue` (landing page)
- `/ide` — `views/Editor.vue` (HOL theory editor and proof IDE)
- `/program` — `views/ProgramIDE.vue` (imperative program verification)
- `/manual` — `views/Manual.vue` (renders `../manual/*.md`)

## Features

- Theory editor over the whole kernel `item_table`: `header`, `type`,
  `typeabbrev`, `quotient`, `datatype`, `constant`, `definition`, `fun`,
  `inductive`, `axiom`, `theorem`.
- Interactive proof IDE on the stable-`#[N]`-ID pipeline
  (`StableProofState`): suggestions / manual / auto tabs, history, open goals.
- Program verification for `.imp` files (Hoare logic VCs).
- Manual reader.

The route/payload contract for the backend is documented in
[`FRONTEND_API.md`](FRONTEND_API.md).
