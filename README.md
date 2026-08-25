# NexusIntrospect

**Proprietary. Copyright (c) 2026 chaosfox26 (Nexus Unleashed). All Rights Reserved.**

A WildStar (build 16042) client addon that makes the game client report its own state —
abilities, stats, nearby units, and its live scripting API — instead of guessing. Read-only.

This is **not** open source. It is licensed separately from, and expressly excluded from, the
MIT license that covers the NexusUnleashed engine. See [`LICENSE.txt`](LICENSE.txt). No right is
granted to copy, modify, redistribute, or reverse-engineer it without written permission.

It ships with the NexusUnleashed server and installs into the WildStar client via the server
launcher, for use on Nexus Unleashed realms.

## Commands

`/nuall` runs everything at once (abilities, stats, nearby units, API surface, telemetry, sprint
probe), then `/reloadui` flushes the capture to disk. Individual commands: `/nuability`, `/nuamp`,
`/nutier`, `/nustat`, `/nucalc`, `/nuscale`, `/nunear`, `/nuintro`, `/nuapi`, `/nuui`, `/nuitem`,
`/nusnap`.

## Private

This repository is private. Updates are pushed here by the maintainers only.
