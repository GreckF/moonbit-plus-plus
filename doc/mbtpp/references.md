# 参考文献

MoonBit++ 的设计与实现所参考的文献。每条注明用在哪里；采用新的文献时在这里补上。

## 语言

1. 用户名可以重复吗. 写给一般月兔用户的MoonBit++入门. 知乎.
   <https://zhuanlan.zhihu.com/p/2067605478985749711>
   — 语言的语法与特性大致来自这篇文章（[proposal.md](proposal.md)）。
2. MoonBit 文档. <https://docs.moonbitlang.com>
   — 语法、`raise`/`try`、`async`、trait、`.mbti` 接口；编译目标（[interop](../../book/src/interop/compile.md)）。

## 类型检查

3. András Kovács. elaboration-zoo. <https://github.com/AndrasKovacs/elaboration-zoo>
   — 基于求值的检查（NbE，项用 de Bruijn 索引、值用层级）、模式合一、插入的元变量
   （`src/tt`，[implementation.md](implementation.md)）。
4. Rocq 参考手册：`match … as … in … return …`. <https://rocq-prover.org/doc/>
   — Rocq 风格的 return 子句（[return-clause](../../book/src/lang/return-clause.md)）。
5. Conor McBride, James McKinna. The View from the Left. Journal of Functional Programming 14(1),
   2004.
   — `with` 抽象：证明中匹配目标里的表达式时，先把它抽象为变量
   （[依赖匹配与细化](../../book/src/lang/dependent-match.md)，`src/tt/elab_match.mbt`）。
6. Agda 用户手册：With-Abstraction.
   <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
   — 同上。

## 代数效应

7. Gordon Plotkin, Matija Pretnar. Handlers of Algebraic Effects. ESOP 2009.
   — 效应与处理器（[effects.md](effects.md)）。
8. Daan Leijen. Type Directed Compilation of Row-Typed Algebraic Effects. POPL 2017.
   — 效应行、效应多态，Koka 的设计（[effects.md](effects.md)）。
9. Ningning Xie, Daan Leijen. Generalized Evidence Passing for Effect Handlers: Efficient
   Compilation of Effect Handlers to C. ICFP 2021.
   — 尾恢复操作按能力（evidence）传递翻译、`ctl` 操作的单子翻译（`src/tt/effects.mbt`、
   `src/tt/ctl.mbt`）。

## 受控展开

10. Daniel Gratzer, Jonathan Sterling, Carlo Angiuli, Thierry Coquand, Lars Birkedal. Controlling
   Unfolding in Type Theory. arXiv:2210.05420. <https://arxiv.org/abs/2210.05420>
   — `#opaque`、`#unfold`、`unfold(f) { e }`（[unfolding.md](unfolding.md)、
   [受控展开](../../book/src/lang/unfolding.md)）。
11. Agda 用户手册：Opaque definitions（Agda 2.6.4 起）.
   <https://agda.readthedocs.io/en/latest/language/opaque-definitions.html>
   — 不用扩展类型、在展开处检查的实现方式；默认透明（[unfolding.md](unfolding.md)）。

## 分阶段元编程

14. Oleg Kiselyov. The Design and Implementation of BER MetaOCaml: System Description. FLOPS 2014,
   LNCS 8475.
   — `code { }` 与 `${ }`（MetaOCaml 的括号与逃逸）、`run`；拼接在代码生成时求值
   （[staging.md](staging.md)，`src/tt/staging.mbt`）。
15. Ningning Xie, Leo White, Olivier Nicole, Jeremy Yallop. MacoCaml: Staging Composable and
   Compilable Macros. ICFP 2023.
   — 阶段 0 的拼接在编译期运行并被生成的代码替换；阶段可以低于 0（[staging.md](staging.md)）。
16. András Kovács. Staged Compilation with Two-Level Type Theory. ICFP 2022. arXiv:2209.09729.
   <https://arxiv.org/abs/2209.09729>
   — 带依赖类型的分阶段：展开就是对生成器求值，转换检查不区分阶段
   （[staging.md](staging.md)，`expand`）。
17. Emir Pašalić, Walid Taha, Tim Sheard. Tagless Staged Interpreters for Typed Languages. ICFP 2002.
   — 用依赖类型写的求值器分阶段后是没有类型标签的编译器（[手册](../../book/src/lang/staging.md)
   与 [examples/staging.mbtpp](../../examples/staging.mbtpp) 中的 `Exp::compile`）。
18. Jun Inoue, Walid Taha. Reasoning about Multi-Stage Programs. ESOP 2012, LNCS 7211.
   — 擦除阶段标注不改变程序的含义：这里作为代码的语义，检查器按它计算（[staging.md](staging.md)）。

## 编译

12. Edwin Brady, Conor McBride, James McKinna. Inductive Families Need Not Store Their Indices.
   TYPES 2003, LNCS 3085.
   — 擦除索引与只用于类型的字段，擦除后形状与 `Nat` 相同的类型用整数表示
   （[编译到 MoonBit](../../book/src/interop/compile.md#nat)，`src/codegen/natlike.mbt`）。
13. Edwin Brady. Idris 2: Quantitative Type Theory in Practice. ECOOP 2021.
   — Idris 2 把形状与 `Nat` 相同的类型编译为整数；同上。
