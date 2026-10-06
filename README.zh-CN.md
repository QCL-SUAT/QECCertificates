# QECCertificates

<div align="center">

![The QECCertificates logo: five qubits on a ring around a checkmark](assets/logo/qeccertificates-logo.svg)

</div>

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

[English](README.md) | **简体中文**

一个用Lean 4写成、由机器检验的量子纠错距离证书库。

## 概述

QECCertificates形式化的是三样东西以及它们的复合：把码参数搜索编码成一个可满足性问题；
对求解器给出的答案作检查、且其可靠性是一条定理的证书检查器；以及编码所依赖的、Pauli算符
的算符树描述与辛描述之间的翻译。每条承重声明都印在审计区里，读者因此能看到它依赖哪些公理，
而不必去相信那个打印出数字的工具。

围绕这条脊柱，本库还携带读**容错陈述**所需的那几层：线路的上链复形及其映射锥与Künneth
公式、时空故障距离、余弦距离、gauging所推广到的辅助超图，以及夹在它们之间的子码层。
此外还有**综合征穷尽的校验矩阵上的抽象闭包定理**——那是每一个重量1译码器所处的那条二分。

本库与导入它的两份配套发展一同开发。它是一个自包含的Lake包：依赖按钉住的revision取用，
一个都不vendored。

## 动机

码参数是搜出来的，而一次搜索以某个求解器的判决收尾。qLDPC Challenge背后的公开schema把
这件事的代价写进了自己的文档：未经认证的距离只报成**上界**——非CSS码是因为其Pauli重量
认证器"is not available yet"，线路级距离是因为精确档"is deferred future work"——而介于
两者之间的产物，用schema自己的话说，是证据而不是证明。

出路有两条：相信打印出这个数的那个工具，或者让这个数**自带一样第三方能检查的东西**。
本库走第二条路，且只做形式化那一侧：搜索问题的编码、证书检查器的可靠性、以及两者的复合，
都是定理。

## 仓库结构

| 层 | 内容 |
|---|---|
| `QECCertificates/GF2/` | GF(2)线性代数：可信行消元、核基、秩证书、对偶见证、精确距离的夹逼、证书规模、超图积与提升乘积、Künneth公式 |
| `QECCertificates/Pauli/` | 算符树↔辛表示的翻译 |
| `QECCertificates/Reflect/` | 证书框架：内核复核的LRAT/RUP检查器及其可靠性定理、双向的编码忠实性——CNF的一个模型**就是**一个轻逻辑算符——保持不可满足性的对称性破缺，以及本库用到的那几条求解器证书的逐条回放 |
| `QECCertificates/Codes/` | 码论层：稳定子码、CSS码与子系统码；gauging与测量协议的表示；共享实例族（Bacon–Shor、BB、HGP、提升乘积）；综合征穷尽的校验矩阵上的抽象闭包定理 |
| `QECCertificates/Homology/` | GF(2)上的链复形及它们承载的距离：映射锥与其蛇形引理公式、四项故障复形及其Künneth公式、时空故障距离、余弦距离、模扩张、探测器分解、端口函数、辅助超图与子码层 |
| [`tools/check_axioms.py`](tools/check_axioms.py) | 读构建日志，凡`#print axioms`一行点名了三条标准公理之外的公理的声明一律拒绝 |

本包共**77个模块**，审计区覆盖其中**每一条**非私有`theorem`/`lemma`。

## 保证

* 零`sorry`、零自定义公理、零`native_decide`；
* 受审计声明不得依赖`propext`、`Classical.choice`与`Quot.sound`之外的公理；只用到其中一条、一条都不用的，一样算过；
* 证书检查器与任何求解器**不共享一行代码**——UNSAT判决只由公式与证明文件重新推出；
* 可移植由门禁保证：没有机器耦合路径，每个依赖按40位完整revision钉住，全文LF行尾。

## 系统要求

Lean `v4.34.0`（钉在`lean-toolchain`里）与`lakefile.toml`中钉住revision的mathlib，都由
`lake`取用。全量构建需要一台内存宽裕的机器，因为光审计区就要把库里每条定理elaborate一遍。

在本机已有全局Lean检出的机器上，[`setup_links.sh`](setup_links.sh)可以把工程接到那份检出上
——它**按`lake-manifest.json`里的revision选层**而不是按目录名，并在收尾逐条复核——省下一次
下载与一次依赖构建。

## 构建

```bash
env -u LEAN_PATH lake build     # 按钉住的 revision 取 mathlib、Lean-QEC 与 QECLean
```

本包自己有十二个模块的收尾是内核在一个大对象上的归约，单个进程要的内存超过托管runner给得起
的量；预算定在十个GiB，正好给16 GB的runner留出工具链与系统的余量，其中最重的那一个（分离
实例）峰值**77 GiB**。所以持续集成只构建**77个模块里的40个**：凡实测峰值放得进预算的模块，
加上它们import的全部（lake少了依赖就编不动）。它**按import顺序**一次只编一个：预算说的是
**单个进程**的需要，而把一个模块的依赖先编好，编它那一次调用就没有别的东西可调度——否则
lake会按runner的核数把一批模块同时放在飞，那正是内存被吃穿的方式，而那样死掉的作业连一行
错误都不会留下。[`tools/ci_scope.py`](tools/ci_scope.py)记着每个模块的实测峰值、算出这个集合，
并在树与表不一致时失败，所以新模块要先测过才进持续集成。审计区是根模块、根模块import整个库，
因此公理审计按下面「验证」一节在有整库内存的机器上跑、不在runner上跑；每次运行都会打印它没有
覆盖什么。

## 验证

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log   # 逐条受审计声明，不得超出三条标准公理
```

这道门禁拒绝任何超出三条标准公理的声明，并且**把"一条都没审计到"判成失败而不是通过**。后一条
在干净克隆上要紧：**全缓存**构建不会重放`#print axioms`输出，所以若脚本报零条声明，删掉根
模块的`.olean`（或touch它的源文件）再编一次。

## 引用

若在学术工作中使用本库，请引用归档后的那个release。[`CITATION.cff`](CITATION.cff)用机器可读
的形式写着同一份信息。

```bibtex
@software{qeccertificates,
  title     = {{QECCertificates}: checkable distance certificates for quantum
              error correction},
  author    = {An, Shuoming},
  year      = {2026},
  doi       = {10.5281/zenodo.23056679},
  url       = {https://github.com/QCL-SUAT/QECCertificates}
}
```

## 贡献

一次改动怎么做、必须过哪些关，见[`CONTRIBUTING.md`](CONTRIBUTING.md)。概言之：四道静态门禁
及其自检在构建前跑；新模块要补上它的审计区条目与实测峰值。

## 许可

Apache-2.0；见[`LICENSE`](LICENSE)与[`NOTICE`](NOTICE)。三个依赖（mathlib、Lean-QEC、
QECLean）都由`lake`按钉住的revision取用，本仓库一个都不vendored。

## 支持

问题与缺陷报告走[issue跟踪器](https://github.com/QCL-SUAT/QECCertificates/issues)。报告里
带上所钉的revision与构建日志末尾，最快得到有效回应。支持为尽力而为：没有服务等级承诺，开
issue前先按上面的「构建」一节自查一遍。
