# Case-study 展示与重写标准

状态：**APPROVED with four clarifications**。
草案基线：`e2c8a57`；四项澄清以 `e969912` 为迁移前基线。
已获准按下述分类持续重构，进度记录于 `CASE_STUDY_REFACTOR.md`。

## 1. 目标与非目标

目标是让读者从一个主要文件看清：程序做什么、规格是什么、如何用
PTree 代数把程序变成规格，以及结论依赖哪些真正的概率分析。

**评价单位是可解释的程序变换，不是行数或 rewrite tactic 的数量。**
主证明不能退化成调用一个已经证明了整个结论的包装引理；辅助引理也
不能把同样的底层展开和同余操作层层藏起来。

本轮不重设计概率接口、canonical routing、FreeOmega、执行器或
MathComp 的信任边界，也不要求所有例子覆盖所有框架功能。

## 2. 接口获取与关系选择

每个 case 文件开头明确四件事：native/frontier profile、使用的关系、
effects/handlers、主结论与适用范围。

另外声明文件角色和 proof mode，不把所有例子强制归为同一种证明：

| Proof mode | 主贡献及验收重点 |
| --- | --- |
| algebraic rewriting | 完整程序的代数变换链 |
| relational/coinductive | 明确的 relation/invariant；局部程序变换优先代数化 |
| analysis-dominated | 概率定理；提供干净的程序端分析消费接口 |
| execution/validation | 实际执行入口及其已证明保证，区分实验与概率证明 |

混合案例可标主次 mode，但不能用分类掩盖本可复用代数的重复证明。

- 程序定义使用 `PTree`；等式推理使用 `Eq` / `PTreeFacts` 或明确的
  theorem owner。具体 backend 显式导入，不能依赖偶然的传递导入或
  export 顺序来决定语义。
- 仅按需要导入 handler、采样、观察和执行模块。不要要求每个例子都
  导入完整内部实现，也不重新引入一层别名 facade。
- backend/profile 与重写注册在统一的 setup 区域确定；证明正文尽量
  不重复 `FI/MX/FO` 等参数。推断确实有歧义时允许显式参数，不能靠
  广泛 hints、增大超时或猜测返回关系来掩盖问题。
- 允许已有 canonical notation，也允许为明确固定 profile 的 raw
  `peutt` 声明局部记号；同一个展示区使用一致含义，并说明选择。
  不要求另造 `canonical_peutt` 包装或修改现有 routing。
- structural 与 observable FreeOmega 不能因 import 顺序混用。
  内部分析如确需 structural interpretation，应有独立作用域和说明。
- 普通 contexts 的 Proper 使用库中已有的 generic theorem；必要的
  backend 注册放在可选库模块，不在每个 case 复制实例。
- 确实涉及本例程序组合子的 congruence 可留在本例，但默认局部可用；
  跨例复用才考虑 export。不为减少主证明行数添加新公理或新 class。
- 标准 effects 优先复用已有定义；自定义协议事件留在本例。

### 2.1 后端只在边界确定，正文消费抽象代数

**选择具体 backend，不意味着主证明应使用具体 backend 的实现接口。**
确定 profile 后，程序组合和代数变换优先通过现有抽象接口完成；本例的
小代数引理也遵循同一规则。

具体构造器允许用于分布定义和 backend-specific analysis，例如
`fair : EnumQ bool` 或 `bernoulli q : SubEnumQ bool`。限制针对高层
程序变换：性质一旦证明，主 calculation 消费该性质而不重开表示。
不要为了外观抽象再造一层无价值 wrapper。

- `EnumQ`、`SubEnumQ`、`SubEnumR`、MathComp 等具体 carrier 名、instance
  和 native/frontier 配置集中在 Setup；需要时使用透明局部记号表达
  tree、distribution 和 relation。仍须明确区分 native 与 frontier，
  不能因为隐藏长参数而选错 `SemanticMeasure` 或关系解释。
- 程序正文使用 `Ret` / `bind` / `Prob` / `Vis` / `iter` 等程序接口；
  分布代数使用已选定 native interpretation 的 `sem_ret`、`sem_bind`、
  `sem_eq`、`sem_lift` 及其现有 laws，避免反复出现 `bind_EnumQ`、
  `ret_EnumQ`、raw-list projection、record constructor 和内部证明字段。
- 将实际分布命名为 `fair`、`bernoulli q` 等有数学含义的对象；其具体
  构造、非负性和质量证书放在定义/分析区。命名不替代证明其概率性质，
  也不引入额外的抽象 sampler 公理。
- 主证明只消费这些对象的代数性质和已证明的概率等式。有限分布展开、
  indexed coupling、票据布局、实数积分等确实依赖表示的工作留在
  分析/实现区，并提供可供高层重写的端点。
- 优先使用适当的抽象 equality/lifting，而非依赖具体 record 的 Coq
  equality。已有精确 equality 可以保留为底层计算事实；将其用于抽象
  层时应通过已经证明的接口连接，不能假定任意 lifting 都可反射成
  Coq equality 或 `sem_eq`。
- 这不是只把 `bind_EnumQ` 改一个短名字：若证明仍展开 EnumQ 的列表
  表示，它仍是具体分析。真正的代数 consumer 不应检查这些实现细节。
- 数学上 backend-independent 的引理放在 generic owner，要求实际
  使用的 laws；本例有理权重分析可以保留 `rat` 等自然限定。不要求
  强行将整个 case 参数化到任意 backend，也不因此新增大 capability。
- 某一步确需具体接口时，集中呈现并解释原因；不以隐藏真实后端依赖
  换取“看起来完全抽象”的论文证明。

目标阅读效果是“用一个已验证的概率代数变换程序”，而不是“不断操作
EnumQ 的内部表示”。具体 backend 的身份在文件开头可查，但不成为
主重写链中反复出现的噪声。

## 3. 单个 case 的阅读结构

原则上一个 case 一个主要 `.v` 文件，以 Section 或必要的 Module 分区：

完整模板适用于 **paper case study**。其余文件明确标为 supporting
example、shared analysis、execution demo 或 regression-like example，
只承担相应职责并说明不采用完整模板的原因。

1. **Setup**：接口、profile、记号、自然的参数条件。
2. **Programs**：源程序、规格程序、handlers、必要的命名中间程序。
3. **Local facts / Analysis**：本例需要的局部代数事实、有限分布计算、
   概率分析证书；明确哪些是数学分析而非代数改写。
4. **Main calculation**：论文展示定理及可读的程序变换链。
5. **Consequences**：行为、定量观测、终止性等实际已证明的推论。
6. **Execution hooks**：如有，给出对应执行/抽取入口和保证边界。

这是职责顺序，不强制建立六个 Module。可在文件头提供 theorem 导航，
也可把仅使用一次的短局部事实写进主证明；不重复定义来强求展示顺序。

单文件原则的例外必须有理由：

- 已被多个 case 使用的 VN、Bernoulli、极限分析等不复制进每个文件；
  可以保留独立 analysis owner，主文件列出所消费的准确端点。
- 一个数学上独立且很大的分析发展可以单独保留；不为“单文件”制造
  难以阅读的巨型文件，也不因 LOC 多就自动拆分。
- 抽取驱动、OCaml host、测试和审计仍在各自目录，不塞进理论文件。
- 不把安全例子与 Gate M 合并；不扩张 universe bypass 白名单。

拆并必须保留所有有意义的例子与验证，不只是保留论文最短版本。

## 4. 主证明：以完整程序的代数链为主体

主结论比较真实的源程序和规格程序；可以用透明记号表示完整 handler
栈，但不能用不透明包装隐藏要展示的变换。

主证明应可按以下形式阅读（概念模板，不是已编译的 Rocq 代码）：

```text
完整程序 P0
  ≈ P1    使用一个已验证组件的行为等式
  ≈ P2    bind / sampling / handler / iteration 代数
  ≈ P3    本例的有限分布或局部程序等式
  ≈ Spec  第二个分析证书或代数化简
```

- 主要程序变换由 `rewrite` / `setoid_rewrite` 表达；需要可见中间项时
  允许命名中间程序或 `transitivity`，不以“全篇只能 rewrite”为目标。
- Proper 在幕后将等式传过 bind、循环和 handlers；不在主证明逐层
  `apply ...Proper` 手工拆开整套 context。
- `unfold` / `cbn` 只暴露当前变换所需的程序结构，不展开 GFP、
  stable-hitting 构造或 measure instance 来完成高层代数。
- `change` / `fold` 允许用于真实的定义转换或可读性改善，但必须有
  明确作用；不保留已验证可去掉的机械整形步骤。
- 局部断言应是一条有意义的程序等式或 pointwise relation，而非
  单纯为穿过又一层包装再重复一遍当前目标。
- 主证明可用 `intros`、分情况、`reflexivity`、少量 side-condition
  tactics；不要把 tactic 词频当作代数化程度。
- 涉及循环体/continuation 的改写优先使用 pointwise relation，
  不为将逐点等式改成函数 Coq equality 而引入函数外延性步骤。

不是每个 case 都存在无条件的最终 rewrite theorem。若需要 invariant、
coinduction 或 relational closure，应把真实的结构条件说清楚；不得
添加“结论即公理”的接口，也不得改变程序使展示更容易。

## 5. 小引理：同样遵循代数接口

按职责区别处理，而不是一律要求短证明：

| 类别 | 建议 statement / proof | owner |
| --- | --- | --- |
| 通用代数/同余 | 对实际需要的语义能力泛化，复用已有定理 | generic Eq / Interp / Prob |
| 本例局部程序变换 | `fragment ≈ replacement` 或逐点版本；展开少量定义后重写 | 本例主文件 |
| 本例 context 的同余 | 复用 generic congruence；只承担应用组合子的提升 | 本例，通常局部 |
| 有限分布计算 | expectation / measure / distribution equality；正常数学计算 | 本例或已有分布库 |
| 无限概率分析 | 收敛、质量、hitting、coupling 等准确端点；允许 induction/coinduction/analysis | 本例分析区或共享分析库 |

本例的小代数引理应尽量可独立作为 rewrite rule 使用：方向清楚、侧条件
自然、结果关系明确。不要套多层近乎同义的 lemma；不要把整个主定理
搬到名为 `helper` 的引理里。

如果发现重复出现、真正 backend-independent 的低层代数缺口，先补到
generic owner，再由 case 消费。若能力确实不足，记录缺口和限定，不为
“全部改成 rewrite”重复 backend 证明或扩大基础假设。

## 6. 假设、结论与论文诚实性

- 主接口使用用户自然理解的条件。例如两枚有效偏置概率分别严格正，
  内部推导非负性及乘积正；不要同时要求用户提供这些冗余证明。
- 保留原定理强度与适用范围；不为了推断方便把异质关系降成 `eq`，
  或把任意 rational target 降成固定常数。
- 明确区分结构等价、`peutt`、transition bisimulation、分布相等、
  几乎必然终止及定量结论，不在论文叙事中互相替代。
- 不声称 rewrite proof 无公理依赖；分别说明正文是否调用外延性，
  和整个定理 `Print Assumptions` 实际继承了什么。
- 区分已证明的有限 runner/极限对应与 fuel-free simulator 的实验，
  不将 PRNG、统计频率或 host execution 冒充形式化概率正确性。
- MathComp 原有显式数学条件与 Gate M 标识必须保留；不追求实例表面
  对称，也不把普通 MathComp 程序定义文件误标为 unchecked assembly。

每个论文候选 case 至少标出：主定理、核心 rewrite 链、外部分析端点、
backend 与假设、明确未声称的性质、可选的运行入口。

## 7. 当前覆盖范围与候选顺序

以下来自当前 `theories/Examples` 文件盘点，不是逐证明完成度验收。
所有现有 Examples 都要获得文件角色、proof mode 和
“按标准改写 / 已符合 / 分析例外”的明确结论；并非都升级为论文主案例。
Regression 不自动纳入论文 case 迁移，也不删其负向测试。

| 批次 / case family | 当前文件 | 审查重点 |
| --- | --- | --- |
| 试点 | `FactoryController.v` | 完整 context 下可读的 rewrite 主线，而非只缩减局部断言 |
| 短篇解释案例 | `ITreeSampling.v`, `EffectInteractions.v` | elaboration / handler 代数，避免手工构造证明替代已有定律 |
| State / execution | `StateCounter.v`, `RationalState.v`, `StateRewrite.v` | 程序重写与执行验证分责；评估合并为一 case 的收益及 extraction 客户端 |
| 组件与工厂 | `BernoulliFactory/BernoulliFactory.v`, `BernoulliFactoryComposition.v`, `BernoulliFactoryProbability.v` | 主要 composition 展示收敛，避免重复通用 bind/Prob 证明 |
| 工厂共享分析 | 同目录 `VonNeumannUnbounded.v`, `RationalBernoulli.v`, `OperationalVonNeumann.v`, `OperationalRationalBernoulli.v`, `OperationalBernoulliFactory.v` | 保留必要概率分析；整理其面向 rewrite 的端点，不强求把极限证明改成重写 |
| 实权采样变体 | 同目录 `RealBernoulliOracle.v`, `RealBernoulliMathComp.v` | 接口条件、与有理模型的关系、数学与 backend 实现边界 |
| 无限协议 | `InteractiveVonNeumann/InteractiveVonNeumannService.v`, `MixedHeadProtocol.v` | 尽可能复用组件等式；真正需要的 coinduction/coupling 单独标明 |
| 随机游走 | `RandomWalk.v` | passage/control-flow 等式链与 harmonic/limit 分析分区 |
| MathComp 程序 | `MathCompPrograms.v` | 明确这是程序定义/方程还是完整 case；链接已有安全/直接验证端点，不凭空补 claim |

具体合并路径、主定理名、需要补充的 generic lemma，逐批读取证明后确定。
不得将本表理解成已经授权删除任何文件或冻结上述分组为新目录结构。

## 8. 逐 case 验收与推进纪律

开始前列出程序、主端点、消费者、当前类型/假设以及保留的分析证书。
完成后给出 before/after 主证明与一张小的 theorem/interface 变更表。

契约分为两类：

- **Stable endpoint**：主论文 theorem、被外部消费的 theorem、extraction
  root、公开概率结果；保持其 statement/strength、运行含义及假设边界。
- **Internal helper**：允许删并、改 statement、移动 owner，但记录职责由
  哪里接替并迁移真实客户端。已登记的 helper snapshot 也应显式处理，
  不能悄悄刷新；不以永久冻结所有 helper 形状阻碍合理清理。

验收要求：

- 主程序变换链能读出来；每一步对应明确的代数定律或分析证书。
- 辅助引理职责清楚，无“主定理藏入 helper”、重复 generic proof 或
  为压行数增加推断魔法；单文件例外有真实复用/信任边界理由。
- 后端配置集中，主证明和小代数引理消费抽象接口；逐项说明仍需具体
  backend 操作的理由，而不是按 `EnumQ` 字样出现次数机械判定合格。
  检查实际选中的 interpretation 和 theorem signature，不只审短记号。
- Stable endpoint 的数学 statement/假设不静默改变。既有 compiled contracts 先比较；
  路径迁移只作明确重定位，不能刷新 snapshot 吞掉差异。
- 不增加 axiom、`Admitted`、theorem-level capability 或 checker bypass。
  若确需加强数学前提或扩张信任边界，停止该项并另报审查。
- 每批做 targeted build、相关客户端/抽取检查及 type/assumption audit；
  公共代数改变时扩大受影响验证。最终做 full build、既有审计/工具测试
  和明确范围的 kernel checks，不把 `-norec` 称为全库递归核验。
- 测试保护定理、语义边界和实际重写入口，不新增大量历史 replay 或
  硬编码 tactic 拼写/行数的审计来约束未来合理证明。
- 按职责清晰的批次提交并推送；保留用户其他工作；默认不查询 CI。

**推进顺序：先完成 FactoryController 试点，将具体 round 计算移出主链；
再按 proof mode 审查全部 case families。分析和执行支持文件不做无谓美化。**
