# QECCertificates

<div align="center">

![The QECCertificates logo: five qubits on a ring around a checkmark](assets/logo/qeccertificates-logo.svg)

</div>

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

[English](README.md) | **简体中文**

## 为什么有它

码参数是搜出来的，而一次搜索以某个求解器的判决收尾。qLDPC Challenge 背后的公开 schema
把这件事的代价写在了自己的文档里：未经认证的距离只报成**上界**——非 CSS 码是因为
Pauli 重量认证器 "is not available yet"，线路级距离是因为精确档 "is deferred future
work"——而介于两者之间的产物，用 schema 自己的话说，是证据而不是证明。

出路有两条：相信打印出这个数的那个工具，或者让这个数**自带一样第三方能检查的东西**。
这个库走第二条路，且只做形式化那一侧：搜索问题的编码、证书检查器的可靠性、以及两者的
复合，都是定理；每条承重声明都印在审计区里，读者能看到它依赖哪些公理。

## 这里有什么

| 层 | 内容 |
|---|---|
| `QECCertificates/GF2/` | GF(2) 线性代数：可信行消元、核基、秩证书、对偶见证、精确距离的夹逼、证书规模、超图积与提升乘积、Künneth 公式 |
| `QECCertificates/Pauli/` | 算符树 ↔ 辛表示的翻译 |
| `QECCertificates/Reflect/` | 证书框架：内核复核的 LRAT/RUP 检查器及其可靠性定理、双向的编码忠实性——CNF 的一个模型**就是**一个轻逻辑算符——保持不可满足性的对称性破缺，以及本库用到的那几条求解器证书的逐条回放 |
| `QECCertificates/Codes/` | 码论层：稳定子码、CSS 码与子系统码；gauging 与测量协议的表示；共享实例族（Bacon–Shor、BB、HGP、提升乘积） |
| [`tools/check_axioms.py`](tools/check_axioms.py) | 读构建日志，凡 `#print axioms` 一行不是恰三条标准公理的声明一律拒绝 |

共 **57 个模块**，审计区覆盖包里**每一条**非私有 `theorem`/`lemma`——本仓库没有审计不到的角落。

## 保证

* 零 `sorry`、零自定义公理、零 `native_decide`；
* 每条受审计声明都恰依赖 `propext`、`Classical.choice` 与 `Quot.sound` 三条；
* 证书检查器与任何求解器**不共享一行代码**——UNSAT 判决只由公式与证明文件重新推出；
* 可移植是要求而不是愿望：没有机器耦合路径，每个依赖按 40 位完整 revision 钉住，全文 LF 行尾。

## 构建

Lean `v4.34.0`（钉在 `lean-toolchain` 里）与 `lakefile.toml` 中钉住 revision 的 mathlib
都由 `lake` 取：

```bash
env -u LEAN_PATH lake build     # 按钉住的 revision 取 mathlib、Lean-QEC 与 QECLean
```

钉住的依赖很重；全量构建需要一台内存宽裕的机器（光审计区就要把库里每条定理 elaborate
一遍）。在本机已有全局 Lean 检出的机器上，[`setup_links.sh`](setup_links.sh) 可以把工程接到
那份检出上——它**按 `lake-manifest.json` 里的 revision 选层**而不是按目录名，并在收尾逐条
复核——省下一次下载与一次依赖构建。

本包自己有十一个模块的收尾是内核在一个大对象上的归约，单个进程要的内存超过托管 runner 给
得起的量；预算定在十个 GiB，正好给 16 GB 的 runner 留出工具链与系统的余量，其中最重的那
个（分离实例）峰值 **77 GiB**。所以持续集成只构建 **57 个模块里的 25 个**：凡实测峰值放得
进预算的模块，加上它们 import 的全部（lake 少了依赖就编不动）。它**按 import 顺序**一次只编
一个：预算说的是**单个进程**的需要，而把一个模块的依赖先编好，编它那一次调用就没有别的东西
可调度——否则 lake 会按 runner 的核数把一批模块同时放在飞，那正是内存被吃穿的方式，而那样
死掉的作业连一行错误都不会留下。
[`tools/ci_scope.py`](tools/ci_scope.py) 记着每个模块的实测峰值、算出这个集合，并在树与表
不一致时失败，所以新模块要先测过才进持续集成。审计区是根模块、根模块 import 整个库，因此
公理审计按下面「验证」一节在有整库内存的机器上跑、不在 runner 上跑；每次运行都会打印它没
覆盖什么。

## 验证

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log   # 逐条受审计声明，只允许三条标准公理
```

这道门禁拒绝任何超出三条标准公理的声明，并且**把"一条都没审计到"判成失败而不是通过**。
后一条在干净克隆上要紧：**全缓存**构建不会重放 `#print axioms` 输出，所以若脚本报零条
声明，删掉根模块的 `.olean`（或 touch 它的源文件）再编一次。

## 引用

若在学术工作中使用本库，请引用归档后的那个 release。[`CITATION.cff`](CITATION.cff) 用机器可读
的形式写着同一份信息。

```bibtex
@software{qeccertificates,
  title     = {{QECCertificates}: certified code parameters and fault distances},
  author    = {An, Shuoming},
  year      = {2026},
  doi       = {10.5281/zenodo.23056679},
  url       = {https://github.com/QCL-SUAT/QECCertificates}
}
```

## 许可

Apache-2.0；见 [`LICENSE`](LICENSE) 与 [`NOTICE`](NOTICE)。三个依赖（mathlib、Lean-QEC、
QECLean）都由 `lake` 按钉住的 revision 取用，本仓库一个都不 vendored。如何贡献见
[`CONTRIBUTING.md`](CONTRIBUTING.md)。
