# Installation

Requirements:

- Node.js (18 or newer).
- The MoonBit toolchain `moon`, a version that uses `moon.mod` / `moon.pkg` (2026-10 or later).

## Installing a release

Every version on the [Releases](https://github.com/GreckF/mbtpp/releases) page comes with an npm
package:

```bash
npm install -g https://github.com/GreckF/mbtpp/releases/download/v0.7.1/moonpp-0.7.1.tgz
moonpp version
```

Pushing a `v*` tag makes GitHub Actions test, build, and publish a release
(`.github/workflows/release.yml`).

## Installing from source

In the repository root:

```bash
moon build --target js --release
npm install -g .
```

`npm install -g .` installs a link to this repository, so to update later, just rerun
`moon build --target js --release`; `npm uninstall -g moonpp` uninstalls it. You can also call
`bin/moonpp` directly (`bin\moonpp.cmd` on Windows).

`moonpp` runs in a Node worker with a large stack (the type checker and interpreter recurse deeply).
