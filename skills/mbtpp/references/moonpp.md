# moonpp 的使用

## 安装

需要 Node.js 18 以上，以及使用 `moon.mod` / `moon.pkg` 的新版 MoonBit 工具链 `moon`（编译、依赖时用）。

```bash
npm install -g https://github.com/GreckF/mbtpp/releases/download/v0.7.1/moonpp-0.7.1.tgz
moonpp version
```

最新版本见 https://github.com/GreckF/mbtpp/releases 。从源码安装：在仓库根目录
`moon build --target js --release` 后 `npm install -g .`。

## 命令

| 命令 | 作用 |
| --- | --- |
| `moonpp new <名字>` | 创建项目 |
| `moonpp check [路径]` | 类型检查项目、包目录或单个文件；提示可以标 `#mbt` 的 `pub` 声明 |
| `moonpp fix [路径]` | 给这些声明加 `#mbt`（检查失败时还原） |
| `moonpp run [路径]` | 用解释器运行 main 包（或指定的包、文件） |
| `moonpp run --compiled [路径] [-- 参数…]` | 编译到 MoonBit 后用 `moon run` 运行，`--` 后的参数传给程序 |
| `moonpp test [路径]` | 用解释器运行 `test "名字" { … }` 块 |
| `moonpp build [路径] [-o 目录]` | 编译成 MoonBit 项目并 `moon build` |
| `moonpp add <user/module[@版本]>` | 添加依赖（`moon add`）并生成缺少的 `.mbti` |
| `moonpp remove <module>` | 删除依赖 |
| `moonpp install` | 安装依赖并生成接口 |
| `moonpp interfaces` | 为已下载的依赖生成缺失的接口 |
| `moonpp tree` | 依赖树 |
| `moonpp ide <文件> [--overlay <json>]` | 编辑器用：错误、类型、目标的 JSON |
| `moonpp version` | 版本 |

选项：`--verbose`（列出导入时跳过的接口项）、`--no-prelude`、`--compiled`、`-o`/`--output <目录>`。

路径可以是单个 `.mbtpp` 文件；旁边有 `moon.pkg` 时其中的导入生效，编译结果在
`<文件目录>/_mbtpp_build/<文件名>/`。

## 项目结构

```text
hello/
  moon.mod            模块：名字、版本、依赖、source 目录
  src/
    main/
      moon.pkg        包：导入的 MoonBit 包、是否是 main 包、检查顺序
      main.mbtpp      一个包可以有多个 .mbtpp 文件，共享一个作用域
  mbtpp_out/          moonpp build 的输出
```

`moon.mod`：

```text
name = "username/hello"

version = "0.1.0"

import {
  "moonbitlang/async@0.22.7",
}

source = "src"
```

`moon.pkg`：

```text
import {
  "moonbitlang/async",
  "moonbitlang/core/string" @str,
}

options(
  "is-main": true,
  "mbtpp-order": [ "shapes.mbtpp" ],
)
```

- `import` 列出包用到的 MoonBit 包；`@别名` 可选，默认取路径最后一段。
- main 包用 `"is-main": true`（`moon fmt` 改写成的 `pkgtype(kind: "executable")` 也认）。
- `"mbtpp-order"`：先检查列出的文件。文件默认按文件名字典序检查，证明需要计算的函数必须在先检查的
  文件中。
- 旧格式 `moon.mod.json`、`moon.pkg.json` 也能读；新版 `moon` 不接受 `moon.mod.json`，在根目录
  `moon fmt` 迁移。

## 依赖

```bash
moonpp add moonbitlang/x@0.5.7
```

然后**在用到它的包的 `moon.pkg` 中导入具体的包**（`"moonbitlang/x/encoding/percent"`）。

- `moonbitlang/core/*` 不需要添加，直接在 `moon.pkg` 中导入。
- 本地模块：根目录的 `moon.work` 写 `members = [".", "../geo"]`，`moon.mod` 中声明依赖；本地模块需要
  先 `moon info` 生成 `.mbti`。
- 导入的项被跳过时用 `moonpp check --verbose` 查看（`not imported:` 列表）。

## 运行与编译

- 解释器（`moonpp run`）不能执行导入的 MoonBit 函数；async 按顺序同步执行。
- `moonpp build` 生成完整的 MoonBit 项目（`moon.mod`、`moon.work`、每个 `.mbtpp` 一个 `.mbt`，加
  `mbtpp_prelude.mbt`、`mbtpp_imports.mbt`、`mbtpp_runtime.mbt`），可以直接构建：

```bash
cd mbtpp_out/main
moon run main --target js
```

- Windows 上 native 目标需要 MSVC Build Tools；没有时用 `--target js`。`moonbitlang/async` 支持
  native、JS、wasm，不支持 wasm-gc。
- 生成的项目总是 main 包，不能生成库包；它带 `{"type": "module"}` 的 `package.json`，JS 产物可以
  直接 `node main.js`。

## 编辑器

VS Code 插件：从 Release 下载 `mbtpp-vscode.vsix`，`code --install-extension mbtpp-vscode.vsix`。
提供诊断、悬停类型、跳转、符号，以及显示 `proof { … }` 中目标的 Info view（Ctrl+Shift+Enter）。
`moonpp` 不在 `PATH` 上时设置 `mbtpp.moonppPath`。

## 常见报错

| 报错 | 原因与处理 |
| --- | --- |
| `unknown name @pkg.f: package @pkg is not imported (list it in the import block of moon.pkg)` | 包没有在 `moon.pkg` 中导入 |
| `unknown name @pkg.f`（包已导入） | 该项没有导入成功，`moonpp check --verbose` 看跳过的项；也可能是名字写错 |
| `cannot run the imported MoonBit function … in the interpreter` | 用 `moonpp run --compiled` |
| `type mismatch` / `expected: … actual: …` | 看规范化后的两边；证明中常见原因是需要归纳、函数是 `#opaque`（看 `hint:`）或检查顺序（看 `hint:`） |
| `match is not exhaustive; missing case(s): …` | 补上列出的分支，或确认它在类型上不可能 |
| `this pattern is not impossible` | 只写模式不写 `=>` 的分支其实可能出现 |
| `checking f took more than 30 s (while evaluating T)` | 定义不终止或计算太大；`#timelimit(秒)`、`#timelimit(none)`，或用 `#opaque` 阻止展开 |
| `hint: f is opaque here; …` | 加 `#unfold(f)` 或 `unfold(f) { … }` |
| `hint: f is defined in x.mbtpp, which is checked after …` | 在 `moon.pkg` 中用 `"mbtpp-order"` 调整顺序 |
| `#mbt fn f cannot be compiled to MoonBit: its body is not in the native fragment: …` | 去掉 `#mbt`，或改写报出的表达式 |
| `cannot construct a value of the MoonBit type @h.T outside its package` | 导入的类型不是 `pub(all)`，只能匹配和传递 |

检查器遇到第一个错误就停止，一次只报一个错误。
