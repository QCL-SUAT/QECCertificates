# QECCertificates

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

[English](README.md) | **简体中文**

**量子纠错码的码参数与故障距离，带证书。**
一个 Lean 4 库：把"信求解器"换成"验证书"。

仓库地址：<https://github.com/QCL-SUAT/QECCertificates>（Apache-2.0，匿名可克隆）。
版本 0.1.0 已打 tag，两个配套开发按完整 commit 钉住它。

**目录：** [为什么有它](#为什么有它) ·
[这里有什么](#这里有什么) · [保证](#保证) ·
[构建](#构建) · [验证](#验证) · [路线图](#路线图) ·
[白皮书](#白皮书) · [由来](#由来) · [许可与引用](#许可与引用)

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

共 **55 个模块**，审计区覆盖包里**每一条**非私有 `theorem`/`lemma`——本仓库没有审计不到的角落。

## 保证

* 零 `sorry`、零自定义公理、零 `native_decide`；
* 每条受审计声明都恰依赖 `propext`、`Classical.choice` 与 `Quot.sound` 三条；
* 证书检查器与任何求解器**不共享一行代码**——UNSAT 判决只由公式与证明文件重新推出；
* 可移植是要求而不是愿望：没有机器耦合路径，每个依赖按 40 位完整 revision 钉住，全文 LF 行尾。

## 构建

```bash
env -u LEAN_PATH lake build     # 按钉住的 revision 取 mathlib、Lean-QEC 与 QECLean
```

钉住的依赖很重；全量构建需要一台内存宽裕的机器（光审计区就要把库里每条定理 elaborate
一遍）。在本机已有全局 Lean 检出的机器上，[`setup_links.sh`](setup_links.sh) 可以把工程接到
那份检出上——它**按 `lake-manifest.json` 里的 revision 选层**而不是按目录名，并在收尾逐条
复核——省下一次下载与一次依赖构建。

## 验证

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log   # 逐条受审计声明，只允许三条标准公理
```

给在干净克隆上跑的人一句提醒：**全缓存**构建不会重放 `#print axioms` 输出，而这道审计门禁
**把"一条都没审计到"判成失败而不是通过**。若脚本报零条声明，删掉根模块的 `.olean`
（或 touch 它的源文件）再编一次。

## 路线图

v0.1 是形式化层本身；共享它的两个配套开发如今把它当依赖消费：它们自己的 GF(2)、Pauli 与
共享码模块已删除，改为按完整 revision 钉住的 import，于是同一批陈述只有一个来源。紧挨
形式化层的证书工具链——距离下界的 CNF 编码器及其已知值闸门、Python 与 C 两份 LRAT/RUP
检查器、以及把校验矩阵变成受认证界的适配器——作为 `python/` 落在下一版，随后是报告其
端到端结果的白皮书。

## 白皮书

[`paper/main.tex`](paper/main.tex) 就是那份白皮书的草稿：库里有什么、其中哪些是机器检验过的、
两个配套开发怎么用它、以及它**刻意不做**什么。用 `latexmk -pdf main.tex` 构建，引用两篇配套
手稿、Lean-QEC 与 qLDPC Challenge schema。

## 由来

本包的共享内核合并自两个配套开发：它们的 GF(2) 与 Pauli 层曾逐文件地互为副本。合并逐文件
记录在那两个仓库的历史里，它们的两篇论文都把本包引作这一层的家。**所有陈述的搬迁没有重写
任何一条证明**——合并表逐文件写明每个模块取自哪一侧、另一侧又贡献了什么。

## 许可与引用

Apache-2.0；见 [`LICENSE`](LICENSE) 与 [`NOTICE`](NOTICE)。引用元数据在 [`CITATION.cff`](CITATION.cff)。
