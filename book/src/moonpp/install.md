# 安装

需要：

- Node.js（18 或更新）。
- MoonBit 工具链 `moon`，使用 `moon.mod` / `moon.pkg` 的版本（2026-10 之后）。

## 安装发布版

[Releases](https://github.com/GreckF/mbtpp/releases) 页面的每个版本都附有 npm 包：

```bash
npm install -g https://github.com/GreckF/mbtpp/releases/download/v0.7.0/moonpp-0.7.0.tgz
moonpp version
```

推送 `v*` tag 时，GitHub Actions 会测试、构建并发布（`.github/workflows/release.yml`）。

## 从源码安装

在仓库根目录：

```bash
moon build --target js --release
npm install -g .
```

`npm install -g .` 安装的是指向本仓库的链接，以后重新运行
`moon build --target js --release` 即可更新；`npm uninstall -g moonpp` 卸载。也可以直接调用
`bin/moonpp`（Windows 上是 `bin\moonpp.cmd`）。

`moonpp` 在一个栈很大的 Node worker 中运行（类型检查器和解释器递归很深）。
