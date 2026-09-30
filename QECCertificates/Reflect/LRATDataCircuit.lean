/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.LRAT

set_option maxRecDepth 1000000

set_option maxHeartbeats 8000000

/-!
# **线路侧**（时间型）SAT 证书的内核回放（由 `tools/gen_circuit_lrat.py` 生成）

本模块是 `Reflect/LRATData.lean` 的**同族兄弟**：码侧那四档的 CNF 断言"不存在轻的
逻辑算符"，本模块的这两档断言"不存在轻的**时空故障**"——《申报指南》方向（八）要的
"量子**线路**的距离判定归约为 SAT"，落点在这里。两档分别是 Bacon–Shor $[[9,1,3]]$
重复测量探测码，与 **BB gauging 测量线路**的时间型探测码。

两档共用同一个探测器形状：$m$ 个校验重复测量 $T$ 轮，一个比特 = 一次
"校验 $a$ 在第 $t$ 轮的**报告结果**"（编号 `T*a + t`），**探测器**取同一校验的
相邻两轮（$H_{(a,t)} = e_{T a + t} + e_{T a + t + 1}$）。故障模式 $f$ 记录哪些
(校验, 轮次) 的结果被翻转，"所有探测器静默"即 $Hf = 0$。核里的非零向量在每个
校验的时间轴上取常值，故**最小不可探测重量恰为 $T$**：一个校验连续 $T$ 轮出错
——时间型分量"不可探测时长 = 轮数"的物理内容。区别只在被重复测量的是哪 $m$ 个
校验（前者是 `Codes/TimeLikeInstance.lean` 的三条重复测量校验，后者是
`Codes/GaugeMeasurementInstance.lean` 的 $|V| = 4$ 条 Gauss 律）。

编码与求解都不是本模块做的事：CNF 由 `tools/timelike_server/timelike_sat.py` 调
**码侧同一条** `validate_encoding.build_pair`（Tseitin 链 + 乘积块 + Sinz 顺序计数器）
产出，证书由 `cadical --lrat` 产出，本模块由脚本逐字节翻译——请勿手改，重跑即可再生。

| `bbgauge44` | **BB gauging 测量线路**的时间型探测码（$|V|=4$ 条 Gauss 律、$T=4=d$ 轮）：不存在重量 $\le 3$ 的不可探测时空故障（最小不可探测重量 $=T=4=d$，$d$ 为 gauged 码 $[[24,3,4]]$ 的码距；探测器 = 同一条 Gauss 律相邻两轮的奇偶） |
| `timelike34` | Bacon–Shor $[[9,1,3]]$ 重复测量探测码（$m=3$ 校验、$T=4$ 轮）：不存在重量 $\le 3$ 的不可探测时空故障（最小不可探测重量 $=T=4$；探测器 = 同一校验相邻两轮的奇偶） |

**`bbgauge44` 档的规模取舍（诚实边界）**：这一档只编码 **gauging 测量那一步**的
$|V| = 4$ 条 Gauss 律的重复测量，**不是**整个 gauged 码 $[[24,3,4]]$ 的 13 条 X 校验 /
12 条 Z 校验的完整综合征提取循环——后者的 CNF 会大到超出内核回放预算。被重复测量的
那 4 个算符逐字钉在 `Codes/GaugeMeasurementInstance.lean` 的 `bbGauge44Checks` 上
（= `Codes/BB24Gauged.lean` 的 `bb24Hx` 第 $9..12$ 行，即 $K_4$ 上的 Gauss 律
$A_v = X_v\prod_{e \ni v}X_e$）。同理，本档问的是**时间型分量**（相邻轮的奇偶），
不含轮内的空间型校验。

**成本口径**：内核回放的成本由 **hint 条数 × 最长子句长度**划定，**不是**引理条数
（`tools/probeA/lrat_scale_probe.py` 的口径）。本模块两档实测 bbgauge44 共 102 步 / 308 条 hint、最长子句 3 个字面量、证书 2405 B、成本代理 924；timelike34 共 74 步 / 224 条 hint、最长子句 3 个字面量、证书 1711 B、成本代理 672。

**边界（与码侧逐字同款）**：本模块证明的是**该 CNF 不可满足**。从"CNF 不可满足"到
"该协议没有重量 $\le T-1$ 的不可探测时空故障"还差**编码忠实性**那一步，它由
①编码器的双向验收（`timelike_sat.py` 的 UNSAT/SAT 两个方向 + 强制赋值探针）、
②`tools/timelike_server/verify_timelike.py` 的第二路对账（独立重建行表 + 全空间枚举）、
③库内 `Reflect/FaithfulCircuit.lean` 的 `buildPair` 同一性等式共同承担，**不在本模块内**。
端到端不含求解器、不含 `native_decide`、不含任何自定义公理。
-/

namespace QECCertificates.LRAT

/-! ## 一、实例 -/
/-- bbgauge44：编码器产出的 CNF（133 变量 / 382 子句）。 -/
def bbgauge44CNF : CNF :=
[
  [(0,false),(1,false),(32,false)], [(0,false),(1,true),(32,true)], [(0,true),(1,false),(32,true)], [(0,true),(1,true),(32,false)],
  [(32,false)], [(1,false),(2,false),(33,false)], [(1,false),(2,true),(33,true)], [(1,true),(2,false),(33,true)],
  [(1,true),(2,true),(33,false)], [(33,false)], [(2,false),(3,false),(34,false)], [(2,false),(3,true),(34,true)],
  [(2,true),(3,false),(34,true)], [(2,true),(3,true),(34,false)], [(34,false)], [(4,false),(5,false),(35,false)],
  [(4,false),(5,true),(35,true)], [(4,true),(5,false),(35,true)], [(4,true),(5,true),(35,false)], [(35,false)],
  [(5,false),(6,false),(36,false)], [(5,false),(6,true),(36,true)], [(5,true),(6,false),(36,true)], [(5,true),(6,true),(36,false)],
  [(36,false)], [(6,false),(7,false),(37,false)], [(6,false),(7,true),(37,true)], [(6,true),(7,false),(37,true)],
  [(6,true),(7,true),(37,false)], [(37,false)], [(8,false),(9,false),(38,false)], [(8,false),(9,true),(38,true)],
  [(8,true),(9,false),(38,true)], [(8,true),(9,true),(38,false)], [(38,false)], [(9,false),(10,false),(39,false)],
  [(9,false),(10,true),(39,true)], [(9,true),(10,false),(39,true)], [(9,true),(10,true),(39,false)], [(39,false)],
  [(10,false),(11,false),(40,false)], [(10,false),(11,true),(40,true)], [(10,true),(11,false),(40,true)], [(10,true),(11,true),(40,false)],
  [(40,false)], [(12,false),(13,false),(41,false)], [(12,false),(13,true),(41,true)], [(12,true),(13,false),(41,true)],
  [(12,true),(13,true),(41,false)], [(41,false)], [(13,false),(14,false),(42,false)], [(13,false),(14,true),(42,true)],
  [(13,true),(14,false),(42,true)], [(13,true),(14,true),(42,false)], [(42,false)], [(14,false),(15,false),(43,false)],
  [(14,false),(15,true),(43,true)], [(14,true),(15,false),(43,true)], [(14,true),(15,true),(43,false)], [(43,false)],
  [(44,false),(0,true)], [(44,false),(16,true)], [(44,true),(0,false),(16,false)], [(45,false),(1,true)],
  [(45,false),(17,true)], [(45,true),(1,false),(17,false)], [(46,false),(2,true)], [(46,false),(18,true)],
  [(46,true),(2,false),(18,false)], [(47,false),(3,true)], [(47,false),(19,true)], [(47,true),(3,false),(19,false)],
  [(48,false),(4,true)], [(48,false),(20,true)], [(48,true),(4,false),(20,false)], [(49,false),(5,true)],
  [(49,false),(21,true)], [(49,true),(5,false),(21,false)], [(50,false),(6,true)], [(50,false),(22,true)],
  [(50,true),(6,false),(22,false)], [(51,false),(7,true)], [(51,false),(23,true)], [(51,true),(7,false),(23,false)],
  [(52,false),(8,true)], [(52,false),(24,true)], [(52,true),(8,false),(24,false)], [(53,false),(9,true)],
  [(53,false),(25,true)], [(53,true),(9,false),(25,false)], [(54,false),(10,true)], [(54,false),(26,true)],
  [(54,true),(10,false),(26,false)], [(55,false),(11,true)], [(55,false),(27,true)], [(55,true),(11,false),(27,false)],
  [(56,false),(12,true)], [(56,false),(28,true)], [(56,true),(12,false),(28,false)], [(57,false),(13,true)],
  [(57,false),(29,true)], [(57,true),(13,false),(29,false)], [(58,false),(14,true)], [(58,false),(30,true)],
  [(58,true),(14,false),(30,false)], [(59,false),(15,true)], [(59,false),(31,true)], [(59,true),(15,false),(31,false)],
  [(44,false),(45,false),(60,false)], [(44,false),(45,true),(60,true)], [(44,true),(45,false),(60,true)], [(44,true),(45,true),(60,false)],
  [(60,false),(46,false),(61,false)], [(60,false),(46,true),(61,true)], [(60,true),(46,false),(61,true)], [(60,true),(46,true),(61,false)],
  [(61,false),(47,false),(62,false)], [(61,false),(47,true),(62,true)], [(61,true),(47,false),(62,true)], [(61,true),(47,true),(62,false)],
  [(62,false),(48,false),(63,false)], [(62,false),(48,true),(63,true)], [(62,true),(48,false),(63,true)], [(62,true),(48,true),(63,false)],
  [(63,false),(49,false),(64,false)], [(63,false),(49,true),(64,true)], [(63,true),(49,false),(64,true)], [(63,true),(49,true),(64,false)],
  [(64,false),(50,false),(65,false)], [(64,false),(50,true),(65,true)], [(64,true),(50,false),(65,true)], [(64,true),(50,true),(65,false)],
  [(65,false),(51,false),(66,false)], [(65,false),(51,true),(66,true)], [(65,true),(51,false),(66,true)], [(65,true),(51,true),(66,false)],
  [(66,false),(52,false),(67,false)], [(66,false),(52,true),(67,true)], [(66,true),(52,false),(67,true)], [(66,true),(52,true),(67,false)],
  [(67,false),(53,false),(68,false)], [(67,false),(53,true),(68,true)], [(67,true),(53,false),(68,true)], [(67,true),(53,true),(68,false)],
  [(68,false),(54,false),(69,false)], [(68,false),(54,true),(69,true)], [(68,true),(54,false),(69,true)], [(68,true),(54,true),(69,false)],
  [(69,false),(55,false),(70,false)], [(69,false),(55,true),(70,true)], [(69,true),(55,false),(70,true)], [(69,true),(55,true),(70,false)],
  [(70,false),(56,false),(71,false)], [(70,false),(56,true),(71,true)], [(70,true),(56,false),(71,true)], [(70,true),(56,true),(71,false)],
  [(71,false),(57,false),(72,false)], [(71,false),(57,true),(72,true)], [(71,true),(57,false),(72,true)], [(71,true),(57,true),(72,false)],
  [(72,false),(58,false),(73,false)], [(72,false),(58,true),(73,true)], [(72,true),(58,false),(73,true)], [(72,true),(58,true),(73,false)],
  [(73,false),(59,false),(74,false)], [(73,false),(59,true),(74,true)], [(73,true),(59,false),(74,true)], [(73,true),(59,true),(74,false)],
  [(74,true)], [(0,false),(75,true)], [(75,false),(0,true)], [(75,false),(76,true)],
  [(1,false),(76,true)], [(76,false),(75,true),(1,true)], [(75,false),(1,false),(77,true)], [(77,false),(1,true)],
  [(77,false),(75,true)], [(76,false),(78,true)], [(2,false),(78,true)], [(78,false),(76,true),(2,true)],
  [(77,false),(79,true)], [(76,false),(2,false),(79,true)], [(79,false),(77,true),(2,true)], [(79,false),(77,true),(76,true)],
  [(77,false),(2,false),(80,true)], [(80,false),(2,true)], [(80,false),(77,true)], [(78,false),(81,true)],
  [(3,false),(81,true)], [(81,false),(78,true),(3,true)], [(79,false),(82,true)], [(78,false),(3,false),(82,true)],
  [(82,false),(79,true),(3,true)], [(82,false),(79,true),(78,true)], [(80,false),(83,true)], [(79,false),(3,false),(83,true)],
  [(83,false),(80,true),(3,true)], [(83,false),(80,true),(79,true)], [(80,false),(3,false),(84,true)], [(84,false),(3,true)],
  [(84,false),(80,true)], [(81,false),(85,true)], [(4,false),(85,true)], [(85,false),(81,true),(4,true)],
  [(82,false),(86,true)], [(81,false),(4,false),(86,true)], [(86,false),(82,true),(4,true)], [(86,false),(82,true),(81,true)],
  [(83,false),(87,true)], [(82,false),(4,false),(87,true)], [(87,false),(83,true),(4,true)], [(87,false),(83,true),(82,true)],
  [(84,false),(88,true)], [(83,false),(4,false),(88,true)], [(88,false),(84,true),(4,true)], [(88,false),(84,true),(83,true)],
  [(85,false),(89,true)], [(5,false),(89,true)], [(89,false),(85,true),(5,true)], [(86,false),(90,true)],
  [(85,false),(5,false),(90,true)], [(90,false),(86,true),(5,true)], [(90,false),(86,true),(85,true)], [(87,false),(91,true)],
  [(86,false),(5,false),(91,true)], [(91,false),(87,true),(5,true)], [(91,false),(87,true),(86,true)], [(88,false),(92,true)],
  [(87,false),(5,false),(92,true)], [(92,false),(88,true),(5,true)], [(92,false),(88,true),(87,true)], [(89,false),(93,true)],
  [(6,false),(93,true)], [(93,false),(89,true),(6,true)], [(90,false),(94,true)], [(89,false),(6,false),(94,true)],
  [(94,false),(90,true),(6,true)], [(94,false),(90,true),(89,true)], [(91,false),(95,true)], [(90,false),(6,false),(95,true)],
  [(95,false),(91,true),(6,true)], [(95,false),(91,true),(90,true)], [(92,false),(96,true)], [(91,false),(6,false),(96,true)],
  [(96,false),(92,true),(6,true)], [(96,false),(92,true),(91,true)], [(93,false),(97,true)], [(7,false),(97,true)],
  [(97,false),(93,true),(7,true)], [(94,false),(98,true)], [(93,false),(7,false),(98,true)], [(98,false),(94,true),(7,true)],
  [(98,false),(94,true),(93,true)], [(95,false),(99,true)], [(94,false),(7,false),(99,true)], [(99,false),(95,true),(7,true)],
  [(99,false),(95,true),(94,true)], [(96,false),(100,true)], [(95,false),(7,false),(100,true)], [(100,false),(96,true),(7,true)],
  [(100,false),(96,true),(95,true)], [(97,false),(101,true)], [(8,false),(101,true)], [(101,false),(97,true),(8,true)],
  [(98,false),(102,true)], [(97,false),(8,false),(102,true)], [(102,false),(98,true),(8,true)], [(102,false),(98,true),(97,true)],
  [(99,false),(103,true)], [(98,false),(8,false),(103,true)], [(103,false),(99,true),(8,true)], [(103,false),(99,true),(98,true)],
  [(100,false),(104,true)], [(99,false),(8,false),(104,true)], [(104,false),(100,true),(8,true)], [(104,false),(100,true),(99,true)],
  [(101,false),(105,true)], [(9,false),(105,true)], [(105,false),(101,true),(9,true)], [(102,false),(106,true)],
  [(101,false),(9,false),(106,true)], [(106,false),(102,true),(9,true)], [(106,false),(102,true),(101,true)], [(103,false),(107,true)],
  [(102,false),(9,false),(107,true)], [(107,false),(103,true),(9,true)], [(107,false),(103,true),(102,true)], [(104,false),(108,true)],
  [(103,false),(9,false),(108,true)], [(108,false),(104,true),(9,true)], [(108,false),(104,true),(103,true)], [(105,false),(109,true)],
  [(10,false),(109,true)], [(109,false),(105,true),(10,true)], [(106,false),(110,true)], [(105,false),(10,false),(110,true)],
  [(110,false),(106,true),(10,true)], [(110,false),(106,true),(105,true)], [(107,false),(111,true)], [(106,false),(10,false),(111,true)],
  [(111,false),(107,true),(10,true)], [(111,false),(107,true),(106,true)], [(108,false),(112,true)], [(107,false),(10,false),(112,true)],
  [(112,false),(108,true),(10,true)], [(112,false),(108,true),(107,true)], [(109,false),(113,true)], [(11,false),(113,true)],
  [(113,false),(109,true),(11,true)], [(110,false),(114,true)], [(109,false),(11,false),(114,true)], [(114,false),(110,true),(11,true)],
  [(114,false),(110,true),(109,true)], [(111,false),(115,true)], [(110,false),(11,false),(115,true)], [(115,false),(111,true),(11,true)],
  [(115,false),(111,true),(110,true)], [(112,false),(116,true)], [(111,false),(11,false),(116,true)], [(116,false),(112,true),(11,true)],
  [(116,false),(112,true),(111,true)], [(113,false),(117,true)], [(12,false),(117,true)], [(117,false),(113,true),(12,true)],
  [(114,false),(118,true)], [(113,false),(12,false),(118,true)], [(118,false),(114,true),(12,true)], [(118,false),(114,true),(113,true)],
  [(115,false),(119,true)], [(114,false),(12,false),(119,true)], [(119,false),(115,true),(12,true)], [(119,false),(115,true),(114,true)],
  [(116,false),(120,true)], [(115,false),(12,false),(120,true)], [(120,false),(116,true),(12,true)], [(120,false),(116,true),(115,true)],
  [(117,false),(121,true)], [(13,false),(121,true)], [(121,false),(117,true),(13,true)], [(118,false),(122,true)],
  [(117,false),(13,false),(122,true)], [(122,false),(118,true),(13,true)], [(122,false),(118,true),(117,true)], [(119,false),(123,true)],
  [(118,false),(13,false),(123,true)], [(123,false),(119,true),(13,true)], [(123,false),(119,true),(118,true)], [(120,false),(124,true)],
  [(119,false),(13,false),(124,true)], [(124,false),(120,true),(13,true)], [(124,false),(120,true),(119,true)], [(121,false),(125,true)],
  [(14,false),(125,true)], [(125,false),(121,true),(14,true)], [(122,false),(126,true)], [(121,false),(14,false),(126,true)],
  [(126,false),(122,true),(14,true)], [(126,false),(122,true),(121,true)], [(123,false),(127,true)], [(122,false),(14,false),(127,true)],
  [(127,false),(123,true),(14,true)], [(127,false),(123,true),(122,true)], [(124,false),(128,true)], [(123,false),(14,false),(128,true)],
  [(128,false),(124,true),(14,true)], [(128,false),(124,true),(123,true)], [(125,false),(129,true)], [(15,false),(129,true)],
  [(129,false),(125,true),(15,true)], [(126,false),(130,true)], [(125,false),(15,false),(130,true)], [(130,false),(126,true),(15,true)],
  [(130,false),(126,true),(125,true)], [(127,false),(131,true)], [(126,false),(15,false),(131,true)], [(131,false),(127,true),(15,true)],
  [(131,false),(127,true),(126,true)], [(128,false),(132,true)], [(127,false),(15,false),(132,true)], [(132,false),(128,true),(15,true)],
  [(132,false),(128,true),(127,true)], [(132,false)]
]

/-- bbgauge44：cadical 的 LRAT 证书（102 条引理、全部 RUP、号连续；另有 0 条删除步被忽略——见 `Reflect/LRAT.lean` 与生成器的口径说明）。 -/
def bbgauge44Proof : List LStep :=
[
  ⟨383,[(128,false)],[382,378]⟩, ⟨384,[(124,false)],[383,363]⟩,
  ⟨385,[(120,false)],[384,348]⟩, ⟨386,[(116,false)],[385,333]⟩,
  ⟨387,[(112,false)],[386,318]⟩, ⟨388,[(108,false)],[387,303]⟩,
  ⟨389,[(104,false)],[388,288]⟩, ⟨390,[(100,false)],[389,273]⟩,
  ⟨391,[(96,false)],[390,258]⟩, ⟨392,[(92,false)],[391,243]⟩,
  ⟨393,[(88,false)],[392,228]⟩, ⟨394,[(84,false)],[393,213]⟩,
  ⟨395,[(80,false)],[394,15,186,199,12]⟩, ⟨396,[(2,false)],[10,395,5,8,185,3,175,170]⟩,
  ⟨397,[(1,false)],[396,10,7]⟩, ⟨398,[(3,false)],[396,15,13]⟩,
  ⟨399,[(46,false)],[396,67]⟩, ⟨400,[(0,false)],[397,5,2]⟩,
  ⟨401,[(45,false)],[397,64]⟩, ⟨402,[(77,false)],[397,176]⟩,
  ⟨403,[(47,false)],[398,70]⟩, ⟨404,[(83,false)],[398,395,197]⟩,
  ⟨405,[(44,false)],[400,61]⟩, ⟨406,[(75,false)],[400,171]⟩,
  ⟨407,[(60,false)],[401,405,112]⟩, ⟨408,[(79,false)],[402,396,183]⟩,
  ⟨409,[(76,false)],[406,397,174]⟩, ⟨410,[(61,false)],[407,399,116]⟩,
  ⟨411,[(82,false)],[408,398,193]⟩, ⟨412,[(78,false)],[409,396,180]⟩,
  ⟨413,[(62,false)],[410,403,120]⟩, ⟨414,[(87,false)],[411,404,212]⟩,
  ⟨415,[(81,false)],[412,398,190]⟩, ⟨416,[(86,false)],[415,411,208]⟩,
  ⟨417,[(91,false)],[416,414,227]⟩, ⟨418,[(95,false)],[390,417,30,259,241,27]⟩,
  ⟨419,[(6,false)],[25,418,20,23,240,18,221,203]⟩, ⟨420,[(5,false)],[419,25,22]⟩,
  ⟨421,[(7,false)],[419,30,28]⟩, ⟨422,[(50,false)],[419,79]⟩,
  ⟨423,[(4,false)],[420,20,17]⟩, ⟨424,[(49,false)],[420,76]⟩,
  ⟨425,[(90,false)],[420,416,222]⟩, ⟨426,[(51,false)],[421,82]⟩,
  ⟨427,[(99,false)],[421,418,256]⟩, ⟨428,[(48,false)],[423,73]⟩,
  ⟨429,[(85,false)],[423,415,204]⟩, ⟨430,[(94,false)],[425,419,237]⟩,
  ⟨431,[(63,false)],[428,413,124]⟩, ⟨432,[(89,false)],[429,420,219]⟩,
  ⟨433,[(98,false)],[430,421,252]⟩, ⟨434,[(64,false)],[431,424,128]⟩,
  ⟨435,[(93,false)],[432,419,234]⟩, ⟨436,[(103,false)],[433,427,272]⟩,
  ⟨437,[(65,false)],[434,422,132]⟩, ⟨438,[(97,false)],[435,421,249]⟩,
  ⟨439,[(66,false)],[437,426,136]⟩, ⟨440,[(102,false)],[438,433,268]⟩,
  ⟨441,[(107,false)],[440,436,287]⟩, ⟨442,[(111,false)],[386,441,45,319,301,42]⟩,
  ⟨443,[(10,false)],[40,442,35,38,300,33,281,263]⟩, ⟨444,[(9,false)],[443,40,37]⟩,
  ⟨445,[(11,false)],[443,45,43]⟩, ⟨446,[(54,false)],[443,91]⟩,
  ⟨447,[(8,false)],[444,35,32]⟩, ⟨448,[(53,false)],[444,88]⟩,
  ⟨449,[(106,false)],[444,440,282]⟩, ⟨450,[(55,false)],[445,94]⟩,
  ⟨451,[(115,false)],[445,442,316]⟩, ⟨452,[(52,false)],[447,85]⟩,
  ⟨453,[(101,false)],[447,438,264]⟩, ⟨454,[(110,false)],[449,443,297]⟩,
  ⟨455,[(67,false)],[452,439,140]⟩, ⟨456,[(105,false)],[453,444,279]⟩,
  ⟨457,[(114,false)],[454,445,312]⟩, ⟨458,[(68,false)],[455,448,144]⟩,
  ⟨459,[(109,false)],[456,443,294]⟩, ⟨460,[(119,false)],[457,451,332]⟩,
  ⟨461,[(69,false)],[458,446,148]⟩, ⟨462,[(113,false)],[459,445,309]⟩,
  ⟨463,[(70,false)],[461,450,152]⟩, ⟨464,[(118,false)],[462,457,328]⟩,
  ⟨465,[(123,false)],[464,460,347]⟩, ⟨466,[(127,false)],[382,465,60,379,361,57]⟩,
  ⟨467,[(14,false)],[55,466,50,53,360,48,341,323]⟩, ⟨468,[(13,false)],[467,55,52]⟩,
  ⟨469,[(15,false)],[467,60,58]⟩, ⟨470,[(58,false)],[467,103]⟩,
  ⟨471,[(12,false)],[468,50,47]⟩, ⟨472,[(57,false)],[468,100]⟩,
  ⟨473,[(122,false)],[468,464,342]⟩, ⟨474,[(59,false)],[469,106]⟩,
  ⟨475,[(131,false)],[469,466,376]⟩, ⟨476,[(56,false)],[471,97]⟩,
  ⟨477,[(117,false)],[471,462,324]⟩, ⟨478,[(126,false)],[473,467,357]⟩,
  ⟨479,[(73,true)],[474,169,168]⟩, ⟨480,[(71,false)],[476,463,156]⟩,
  ⟨481,[(121,false)],[477,468,339]⟩, ⟨482,[(130,false)],[478,469,372]⟩,
  ⟨483,[(72,true)],[479,470,164]⟩, ⟨484,[],[480,483,472,160]⟩
]

/-- **bbgauge44 的内核回放**：该 CNF 不可满足（证书逐条在核内复算）。 -/
theorem bbgauge44_unsat : ¬ Satisfiable bbgauge44CNF :=
  unsat_of_checkSteps (steps := bbgauge44Proof) (by decide)

/-- timelike34：编码器产出的 CNF（98 变量 / 279 子句）。 -/
def timelike34CNF : CNF :=
[
  [(0,false),(1,false),(24,false)], [(0,false),(1,true),(24,true)], [(0,true),(1,false),(24,true)], [(0,true),(1,true),(24,false)],
  [(24,false)], [(1,false),(2,false),(25,false)], [(1,false),(2,true),(25,true)], [(1,true),(2,false),(25,true)],
  [(1,true),(2,true),(25,false)], [(25,false)], [(2,false),(3,false),(26,false)], [(2,false),(3,true),(26,true)],
  [(2,true),(3,false),(26,true)], [(2,true),(3,true),(26,false)], [(26,false)], [(4,false),(5,false),(27,false)],
  [(4,false),(5,true),(27,true)], [(4,true),(5,false),(27,true)], [(4,true),(5,true),(27,false)], [(27,false)],
  [(5,false),(6,false),(28,false)], [(5,false),(6,true),(28,true)], [(5,true),(6,false),(28,true)], [(5,true),(6,true),(28,false)],
  [(28,false)], [(6,false),(7,false),(29,false)], [(6,false),(7,true),(29,true)], [(6,true),(7,false),(29,true)],
  [(6,true),(7,true),(29,false)], [(29,false)], [(8,false),(9,false),(30,false)], [(8,false),(9,true),(30,true)],
  [(8,true),(9,false),(30,true)], [(8,true),(9,true),(30,false)], [(30,false)], [(9,false),(10,false),(31,false)],
  [(9,false),(10,true),(31,true)], [(9,true),(10,false),(31,true)], [(9,true),(10,true),(31,false)], [(31,false)],
  [(10,false),(11,false),(32,false)], [(10,false),(11,true),(32,true)], [(10,true),(11,false),(32,true)], [(10,true),(11,true),(32,false)],
  [(32,false)], [(33,false),(0,true)], [(33,false),(12,true)], [(33,true),(0,false),(12,false)],
  [(34,false),(1,true)], [(34,false),(13,true)], [(34,true),(1,false),(13,false)], [(35,false),(2,true)],
  [(35,false),(14,true)], [(35,true),(2,false),(14,false)], [(36,false),(3,true)], [(36,false),(15,true)],
  [(36,true),(3,false),(15,false)], [(37,false),(4,true)], [(37,false),(16,true)], [(37,true),(4,false),(16,false)],
  [(38,false),(5,true)], [(38,false),(17,true)], [(38,true),(5,false),(17,false)], [(39,false),(6,true)],
  [(39,false),(18,true)], [(39,true),(6,false),(18,false)], [(40,false),(7,true)], [(40,false),(19,true)],
  [(40,true),(7,false),(19,false)], [(41,false),(8,true)], [(41,false),(20,true)], [(41,true),(8,false),(20,false)],
  [(42,false),(9,true)], [(42,false),(21,true)], [(42,true),(9,false),(21,false)], [(43,false),(10,true)],
  [(43,false),(22,true)], [(43,true),(10,false),(22,false)], [(44,false),(11,true)], [(44,false),(23,true)],
  [(44,true),(11,false),(23,false)], [(33,false),(34,false),(45,false)], [(33,false),(34,true),(45,true)], [(33,true),(34,false),(45,true)],
  [(33,true),(34,true),(45,false)], [(45,false),(35,false),(46,false)], [(45,false),(35,true),(46,true)], [(45,true),(35,false),(46,true)],
  [(45,true),(35,true),(46,false)], [(46,false),(36,false),(47,false)], [(46,false),(36,true),(47,true)], [(46,true),(36,false),(47,true)],
  [(46,true),(36,true),(47,false)], [(47,false),(37,false),(48,false)], [(47,false),(37,true),(48,true)], [(47,true),(37,false),(48,true)],
  [(47,true),(37,true),(48,false)], [(48,false),(38,false),(49,false)], [(48,false),(38,true),(49,true)], [(48,true),(38,false),(49,true)],
  [(48,true),(38,true),(49,false)], [(49,false),(39,false),(50,false)], [(49,false),(39,true),(50,true)], [(49,true),(39,false),(50,true)],
  [(49,true),(39,true),(50,false)], [(50,false),(40,false),(51,false)], [(50,false),(40,true),(51,true)], [(50,true),(40,false),(51,true)],
  [(50,true),(40,true),(51,false)], [(51,false),(41,false),(52,false)], [(51,false),(41,true),(52,true)], [(51,true),(41,false),(52,true)],
  [(51,true),(41,true),(52,false)], [(52,false),(42,false),(53,false)], [(52,false),(42,true),(53,true)], [(52,true),(42,false),(53,true)],
  [(52,true),(42,true),(53,false)], [(53,false),(43,false),(54,false)], [(53,false),(43,true),(54,true)], [(53,true),(43,false),(54,true)],
  [(53,true),(43,true),(54,false)], [(54,false),(44,false),(55,false)], [(54,false),(44,true),(55,true)], [(54,true),(44,false),(55,true)],
  [(54,true),(44,true),(55,false)], [(55,true)], [(0,false),(56,true)], [(56,false),(0,true)],
  [(56,false),(57,true)], [(1,false),(57,true)], [(57,false),(56,true),(1,true)], [(56,false),(1,false),(58,true)],
  [(58,false),(1,true)], [(58,false),(56,true)], [(57,false),(59,true)], [(2,false),(59,true)],
  [(59,false),(57,true),(2,true)], [(58,false),(60,true)], [(57,false),(2,false),(60,true)], [(60,false),(58,true),(2,true)],
  [(60,false),(58,true),(57,true)], [(58,false),(2,false),(61,true)], [(61,false),(2,true)], [(61,false),(58,true)],
  [(59,false),(62,true)], [(3,false),(62,true)], [(62,false),(59,true),(3,true)], [(60,false),(63,true)],
  [(59,false),(3,false),(63,true)], [(63,false),(60,true),(3,true)], [(63,false),(60,true),(59,true)], [(61,false),(64,true)],
  [(60,false),(3,false),(64,true)], [(64,false),(61,true),(3,true)], [(64,false),(61,true),(60,true)], [(61,false),(3,false),(65,true)],
  [(65,false),(3,true)], [(65,false),(61,true)], [(62,false),(66,true)], [(4,false),(66,true)],
  [(66,false),(62,true),(4,true)], [(63,false),(67,true)], [(62,false),(4,false),(67,true)], [(67,false),(63,true),(4,true)],
  [(67,false),(63,true),(62,true)], [(64,false),(68,true)], [(63,false),(4,false),(68,true)], [(68,false),(64,true),(4,true)],
  [(68,false),(64,true),(63,true)], [(65,false),(69,true)], [(64,false),(4,false),(69,true)], [(69,false),(65,true),(4,true)],
  [(69,false),(65,true),(64,true)], [(66,false),(70,true)], [(5,false),(70,true)], [(70,false),(66,true),(5,true)],
  [(67,false),(71,true)], [(66,false),(5,false),(71,true)], [(71,false),(67,true),(5,true)], [(71,false),(67,true),(66,true)],
  [(68,false),(72,true)], [(67,false),(5,false),(72,true)], [(72,false),(68,true),(5,true)], [(72,false),(68,true),(67,true)],
  [(69,false),(73,true)], [(68,false),(5,false),(73,true)], [(73,false),(69,true),(5,true)], [(73,false),(69,true),(68,true)],
  [(70,false),(74,true)], [(6,false),(74,true)], [(74,false),(70,true),(6,true)], [(71,false),(75,true)],
  [(70,false),(6,false),(75,true)], [(75,false),(71,true),(6,true)], [(75,false),(71,true),(70,true)], [(72,false),(76,true)],
  [(71,false),(6,false),(76,true)], [(76,false),(72,true),(6,true)], [(76,false),(72,true),(71,true)], [(73,false),(77,true)],
  [(72,false),(6,false),(77,true)], [(77,false),(73,true),(6,true)], [(77,false),(73,true),(72,true)], [(74,false),(78,true)],
  [(7,false),(78,true)], [(78,false),(74,true),(7,true)], [(75,false),(79,true)], [(74,false),(7,false),(79,true)],
  [(79,false),(75,true),(7,true)], [(79,false),(75,true),(74,true)], [(76,false),(80,true)], [(75,false),(7,false),(80,true)],
  [(80,false),(76,true),(7,true)], [(80,false),(76,true),(75,true)], [(77,false),(81,true)], [(76,false),(7,false),(81,true)],
  [(81,false),(77,true),(7,true)], [(81,false),(77,true),(76,true)], [(78,false),(82,true)], [(8,false),(82,true)],
  [(82,false),(78,true),(8,true)], [(79,false),(83,true)], [(78,false),(8,false),(83,true)], [(83,false),(79,true),(8,true)],
  [(83,false),(79,true),(78,true)], [(80,false),(84,true)], [(79,false),(8,false),(84,true)], [(84,false),(80,true),(8,true)],
  [(84,false),(80,true),(79,true)], [(81,false),(85,true)], [(80,false),(8,false),(85,true)], [(85,false),(81,true),(8,true)],
  [(85,false),(81,true),(80,true)], [(82,false),(86,true)], [(9,false),(86,true)], [(86,false),(82,true),(9,true)],
  [(83,false),(87,true)], [(82,false),(9,false),(87,true)], [(87,false),(83,true),(9,true)], [(87,false),(83,true),(82,true)],
  [(84,false),(88,true)], [(83,false),(9,false),(88,true)], [(88,false),(84,true),(9,true)], [(88,false),(84,true),(83,true)],
  [(85,false),(89,true)], [(84,false),(9,false),(89,true)], [(89,false),(85,true),(9,true)], [(89,false),(85,true),(84,true)],
  [(86,false),(90,true)], [(10,false),(90,true)], [(90,false),(86,true),(10,true)], [(87,false),(91,true)],
  [(86,false),(10,false),(91,true)], [(91,false),(87,true),(10,true)], [(91,false),(87,true),(86,true)], [(88,false),(92,true)],
  [(87,false),(10,false),(92,true)], [(92,false),(88,true),(10,true)], [(92,false),(88,true),(87,true)], [(89,false),(93,true)],
  [(88,false),(10,false),(93,true)], [(93,false),(89,true),(10,true)], [(93,false),(89,true),(88,true)], [(90,false),(94,true)],
  [(11,false),(94,true)], [(94,false),(90,true),(11,true)], [(91,false),(95,true)], [(90,false),(11,false),(95,true)],
  [(95,false),(91,true),(11,true)], [(95,false),(91,true),(90,true)], [(92,false),(96,true)], [(91,false),(11,false),(96,true)],
  [(96,false),(92,true),(11,true)], [(96,false),(92,true),(91,true)], [(93,false),(97,true)], [(92,false),(11,false),(97,true)],
  [(97,false),(93,true),(11,true)], [(97,false),(93,true),(92,true)], [(97,false)]
]

/-- timelike34：cadical 的 LRAT 证书（74 条引理、全部 RUP、号连续；另有 0 条删除步被忽略——见 `Reflect/LRAT.lean` 与生成器的口径说明）。 -/
def timelike34Proof : List LStep :=
[
  ⟨280,[(93,false)],[279,275]⟩, ⟨281,[(89,false)],[280,260]⟩,
  ⟨282,[(85,false)],[281,245]⟩, ⟨283,[(81,false)],[282,230]⟩,
  ⟨284,[(77,false)],[283,215]⟩, ⟨285,[(73,false)],[284,200]⟩,
  ⟨286,[(69,false)],[285,185]⟩, ⟨287,[(65,false)],[286,170]⟩,
  ⟨288,[(61,false)],[287,15,143,156,12]⟩, ⟨289,[(2,false)],[10,288,5,8,142,3,132,127]⟩,
  ⟨290,[(1,false)],[289,10,7]⟩, ⟨291,[(3,false)],[289,15,13]⟩,
  ⟨292,[(35,false)],[289,52]⟩, ⟨293,[(0,false)],[290,5,2]⟩,
  ⟨294,[(34,false)],[290,49]⟩, ⟨295,[(58,false)],[290,133]⟩,
  ⟨296,[(36,false)],[291,55]⟩, ⟨297,[(64,false)],[291,288,154]⟩,
  ⟨298,[(33,false)],[293,46]⟩, ⟨299,[(56,false)],[293,128]⟩,
  ⟨300,[(45,false)],[294,298,85]⟩, ⟨301,[(60,false)],[295,289,140]⟩,
  ⟨302,[(57,false)],[299,290,131]⟩, ⟨303,[(46,false)],[300,292,89]⟩,
  ⟨304,[(63,false)],[301,291,150]⟩, ⟨305,[(59,false)],[302,289,137]⟩,
  ⟨306,[(47,false)],[303,296,93]⟩, ⟨307,[(68,false)],[304,297,169]⟩,
  ⟨308,[(62,false)],[305,291,147]⟩, ⟨309,[(67,false)],[308,304,165]⟩,
  ⟨310,[(72,false)],[309,307,184]⟩, ⟨311,[(76,false)],[283,310,30,216,198,27]⟩,
  ⟨312,[(6,false)],[25,311,20,23,197,18,178,160]⟩, ⟨313,[(5,false)],[312,25,22]⟩,
  ⟨314,[(7,false)],[312,30,28]⟩, ⟨315,[(39,false)],[312,64]⟩,
  ⟨316,[(4,false)],[313,20,17]⟩, ⟨317,[(38,false)],[313,61]⟩,
  ⟨318,[(71,false)],[313,309,179]⟩, ⟨319,[(40,false)],[314,67]⟩,
  ⟨320,[(80,false)],[314,311,213]⟩, ⟨321,[(37,false)],[316,58]⟩,
  ⟨322,[(66,false)],[316,308,161]⟩, ⟨323,[(75,false)],[318,312,194]⟩,
  ⟨324,[(48,false)],[321,306,97]⟩, ⟨325,[(70,false)],[322,313,176]⟩,
  ⟨326,[(79,false)],[323,314,209]⟩, ⟨327,[(49,false)],[324,317,101]⟩,
  ⟨328,[(74,false)],[325,312,191]⟩, ⟨329,[(84,false)],[326,320,229]⟩,
  ⟨330,[(50,false)],[327,315,105]⟩, ⟨331,[(78,false)],[328,314,206]⟩,
  ⟨332,[(51,false)],[330,319,109]⟩, ⟨333,[(83,false)],[331,326,225]⟩,
  ⟨334,[(88,false)],[333,329,244]⟩, ⟨335,[(92,false)],[279,334,45,276,258,42]⟩,
  ⟨336,[(10,false)],[40,335,35,38,257,33,238,220]⟩, ⟨337,[(9,false)],[336,40,37]⟩,
  ⟨338,[(11,false)],[336,45,43]⟩, ⟨339,[(43,false)],[336,76]⟩,
  ⟨340,[(8,false)],[337,35,32]⟩, ⟨341,[(42,false)],[337,73]⟩,
  ⟨342,[(87,false)],[337,333,239]⟩, ⟨343,[(44,false)],[338,79]⟩,
  ⟨344,[(96,false)],[338,335,273]⟩, ⟨345,[(41,false)],[340,70]⟩,
  ⟨346,[(82,false)],[340,331,221]⟩, ⟨347,[(91,false)],[342,336,254]⟩,
  ⟨348,[(54,true)],[343,126,125]⟩, ⟨349,[(52,false)],[345,332,113]⟩,
  ⟨350,[(86,false)],[346,337,236]⟩, ⟨351,[(95,false)],[347,338,269]⟩,
  ⟨352,[(53,true)],[348,339,121]⟩, ⟨353,[],[349,352,341,117]⟩
]

/-- **timelike34 的内核回放**：该 CNF 不可满足（证书逐条在核内复算）。 -/
theorem timelike34_unsat : ¬ Satisfiable timelike34CNF :=
  unsat_of_checkSteps (steps := timelike34Proof) (by decide)

end QECCertificates.LRAT
