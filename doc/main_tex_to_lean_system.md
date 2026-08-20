# `main.tex` → Lean 系统化翻译索引

> 基线日期：2026-08-21
> 第一阶段范围：全库目录边界、论文总路由、M01--M03 的段落 /
> 公式 / Lean 声明映射。全部 Lean 文件清单见
> [`lean_directory_inventory.md`](lean_directory_inventory.md)。

## 1. 工程约定

### 1.1 权威边界

1. `main.tex` 及 `sections/*.tex` 是非形式化数学来源，不是已检查的证明。
2. `ZetaZero/` 是本项目的 Lean 4 目标库；M01--M10 的稳定公开入口以
   `doc/roadmap.md` 为准。
3. `zeta-23-lean/Zeta23/` 是通过 `lakefile.toml` 接入的外部参考依赖。
   本项目只重用被 `ZetaZero` 实际 import 的声明，不把 `Zeta23` 根库或其
   headline theorem 计为 ZetaZero 主路线成果。
4. 声明名、docstring 和论文描述都不能代替 Lean 检查。本文中的
   “Lean 已证明”只指实际声明的类型与证明项已被当前工具链接受。
5. 不用 `sorry`、`admit`、项目定义的 `axiom`、空 theorem shell 或人为
   过强假设隐藏 gap。条件定理可以是已检查的接口，但其假设若尚未从
   前置节构造，必须标为“仅接口假设”，不得写成论文结论已完成。

### 1.2 状态标记

| 标记 | 含义 |
|---|---|
| **[PAPER]** | 论文声称或纸面证明；本标记不含 Lean 证据。 |
| **[LEAN]** | 有具体 Lean 声明，且当前工作中对相关 source/facade 执行了成功构建。 |
| **[INTERFACE]** | 条件定理本身已证，但所需数学输入尚未由主路线构造。 |
| **[GAP]** | 论文步骤尚无对应 Lean 声明，或尚未被稳定 facade 集成。 |
| **[EXPERIMENT]** | 已有可构建的实验性或通用工具声明，但不宣称完成稳定节点。 |

### 1.3 三级映射单元

每个翻译项必须同时记录：

1. **段落级**：文件、行段或 label，以及该段的数学意图；
2. **公式级**：对象、变量、量词、定义域和隐含条件；
3. **声明级**：Lean 模块/标识符、实际假设、当前状态、证据和
   下一个验收接口。

若发现论文与 Lean 不一致，按以下固定格式记录：

```text
[BUG/GAP-ID]
paper location:
paper claim:
Lean declaration or attempted type:
mismatch / missing hypothesis:
reproduction command:
observed result:
owner node and next acceptance theorem:
```

## 2. 论文总览

### 2.1 `main.tex` 实际输入顺序

| 顺序 | 来源 | 主要 label / 内容 | 稳定节点 |
|---:|---|---|---|
| 1 | `sections/00_main_theorem.tex` | `thm:main`，计数符号与密度一结论 | M10 |
| 2 | `sections/01_invariant_contour.tex` | `sec:common-matrix` | M02 |
| 3 | `sections/02_zero_side.tex` | `sec:zero-side` | M03 |
| 4 | `sections/03_right_edge.tex` | `sec:right-edge` | M04 |
| 5 | `sections/04_stationary.tex` | `sec:stationary` | M04 |
| 6 | `sections/06_threeZ_common_prefix.tex` | `sec:threeZ` | M05 |
| 7 | `sections/07_hlp_local_replacement.tex` | `sec:hlp-local`, `sec:local-projector` | M05 |
| 8 | `sections/08_global_model_floor.tex` | `sec:model-floor` | M06 |
| 9 | `sections/09_divisor_analysis.tex` | `sec:divisor-gram` | M07 |
| 10 | `sections/10_shell_edge.tex` | `sec:shell-frame`, `sec:edge-rank` | M08 |
| 11 | `sections/11_reference_remainder.tex` | `sec:ledger` | M08 |
| 12 | `sections/12_retained_space.tex` | `sec:retained` | M09 |
| 13 | `sections/13_minmax.tex` | `sec:minmax` | M01 |
| 14 | `sections/14_endgame.tex` | `sec:multiplicity-endgame` | M10 |
| 15 | `sections/15_references.tex` | bibliography | 非 Lean 节点 |

`main.tex` 本身只定义文档结构、公共记号并按上表组装论文；其中
`\rank`、`\codim`、`\Ran`、`\spec`、`\Gfr`、`\PT` 等是纸面记号，
必须由各节点中的具体 Lean 定义连接，不因出现在 preamble 就视为已形式化。

### 2.2 M01--M10 稳定路由、验收接口与状态

| ID | 稳定 facade | 本阶段可指向的终端声明 / 验收目标 | 状态（2026-08-21） |
|---|---|---|---|
| M01 | `ZetaZero.FiniteDimensionalInertiaReduction` | `rank_plus_hilbertSchmidt_minmax_after_linearEquiv` 与 `three_quarters_lower_on_physicalGoodSpace` | **[LEAN]** Lean core 完成；Blueprint 完整认证未完成，不是 green。 |
| M02 | `ZetaZero.HardyGaugeInvariantContourForm` | 当前终端 `exists_packetSameForm_zeroSum`；目标是特化为 stationary packet weights 的全局 zero sum | **[LEAN]+[GAP]** contour/zero-sum core 已验证，特化和 good-height 链未完成。 |
| M03 | `ZetaZero.ZeroSideStationaryGeometry` | 当前终端 `straighten_hardyGauge_simpleStationary_iff_zetaOne_simpleZero` 和 `conjugatePair_negativeIndexLE_one`；目标是全局 packet pullback/inertia 恒等式 | **[LEAN]+[GAP]** 局部 residue/block/dictionary 已验证，evaluation surjectivity 与 good-height 未形式化。 |
| M04 | `ZetaZero.RightEdgeArithmeticSource` | `norm_intervalIntegral_stationary_sub_standard_le_sixteen_div_three_mul_inv` 是当前有限窗口终端；目标是实际 packet/Perron source transfer | **[LEAN]+[INTERFACE]** 有限窗口核心存在，全局转移未完成。 |
| M05 | `ZetaZero.HLPLocalModel` | `directCarrier_polynomialWeight_finiteSubset_le`、`completed_leading_cluster`；目标是实际 local projector/principal operator | **[LEAN]+[INTERFACE]** 系数与 carrier 基础存在，packet/Perron 对接缺失。 |
| M06 | `ZetaZero.GlobalModelSpectralFloor` | 当前抽象 `certified_point_zero_six_floor`；论文验收目标是具体 `prop:model-floor` | **[EXPERIMENT]** 抽象 Schur-floor 基础，非具体模型证明。 |
| M07 | `ZetaZero.DivisorGramArithmeticTransfer` | `operatorGcdForm_re_nonnegative`；论文验收目标是带定量损失的 arithmetic transfer | **[EXPERIMENT]** positive/gcd Gram 基础，具体 deformation 未完成。 |
| M08 | `ZetaZero.FrameCompression` | `finrank_range_translatedPoleJets_le`；目标是 shell frame + edge rank + regular ledger 合成 | **[EXPERIMENT]** 有限 feature-rank 基础，主分析链未完成。 |
| M09 | `ZetaZero.RetainedSpace` | `codim_threefold_inf_le`；目标是论文 `eq:retained-codim` | **[EXPERIMENT]** kernel/codimension 抽象记账已有，实际均值映射缺失。 |
| M10 | `ZetaZero.GenericPerturbationMinMaxEndgame` | `density_one_critical_line` | **[INTERFACE]** 从 off-critical little-o 假设到比值极限已证；该 little-o 正是未完成分析输入，因而 M10 不是 green。 |

### 2.3 依赖 DAG

```text
M01 ---------------------------------------------> M10
M02 -> M03 --------------------------------------> M10
  `-> M04 -> M05 -> M06 --.
                  `-> M07 ---+-> M08 -> M09 -----> M10
M03 -------------------------'
```

该图表示数学验收依赖，不等于 Lake import 图。例如 M10 facade 可以 import
尚未 green 的前置 facade，但这不能使前置数学输入自动成立。

## 3. M01 详译：有限维惯性归约

**来源**：`sections/13_minmax.tex:1-64`，`sec:minmax`、`lem:minmax`、
`eq:minmax-good-space`、`eq:minmax`、`eq:minmax-codim`。
**去向**：`ZetaZero.FiniteDimensionalInertiaReduction`。
**验收声明**：
`ZetaZero.FiniteDimensionalInertiaReduction.WhitenedMinMax.rank_plus_hilbertSchmidt_minmax_after_linearEquiv`。
**本阶段证据命令**：`lake build ZetaZero.FiniteDimensionalInertiaReduction` （PASS）。

### 3.1 段落 / 公式 / 声明映射

| 论文位置与意图 | 公式、量词与隐含条件 | Lean 接口与假设对照 | 状态 / gap |
|---|---|---|---|
| `13:4-18`：在有限维 `V` 上分解 `A=P+E+R` | `A,P,E,R,G` Hermitian，`G≻0`，`P⪪c₀G`，`rank E≤r`，`c₀>0`；`R` 以 `G` 白化 | `Basic.lean`: `NonnegativeOn`, `StrictlyNegativeOn`；`WhitenedMinMax.lean` 以实二次型 `Aq Pq Eq Rq Gq`、线性映射 `E`、Hermitian matrix `B` 表示白化余项。`hdecomp`, `hP`, `hEzero`, `hRdiag`, `hGcoord`, `hE` 把纸面算子关系显式化。 | **[LEAN]**。具体后期 reference Gram 到白化坐标的构造不属于 M01，仍是 M08--M10 集成输入。 |
| `13:20-24`：白化 `P,E,R` | `G^{-1/2}` 必须存在且可逆；同余传输保持负指数 | `CongruenceTransport.lean`: `pullbackForm`, `transportedSubspace`, `negativeIndexBound_pullback`；`WhitenedMinMax.lean`: `physicalGoodSpace` 与最终 `...after_linearEquiv` 接受显式 `LinearEquiv` | **[LEAN]/[INTERFACE]**：传输定理已证；实际 `G^{-1/2}` equivalence 由后续节点提供。 |
| `13:25-26`：消去有限秩 `E` | `S_E=Ran E`，因 Hermitian 得 `S_E⊥=ker E`，`dim S_E≤r` | `FiniteRankPerturbation.lean`: `codim_ker_eq_finrank_range`, `codim_ker_le`；`RankPlusGoodSpace.lean`: `negativeIndexBound_rank_plus_goodSpace`；最终定理用 `hEzero` 而非仅依赖名义上的 Hermitian | **[LEAN]**。`hEzero` 是精确的作用条件；应由实际 low-rank 分解证明。 |
| `13:26-30`：对 `R̃` 选坏谱子空间 | `S_R={λ : abs λ ≥ c₀/4}`，`#S_R(c₀/4)²≥...`，即 `#S_R c₀²/16 ≤ ‖R̃‖²_HS` | `SpectralThresholdCount.lean`: `thresholdSet`, `card_thresholdSet_mul_sq_le_sum_sq`；`HermitianThreshold.lean`: `card_badEigenvalues_quarter_le_sixteen` | **[LEAN]**。阈值采用 `≤ -τ` 的负坏特征值，这对下界所需且比纸面 `abs λ ≥ τ` 删除更精确。 |
| `13:27-30`：Hilbert--Schmidt 和谱质量一致 | `s=‖R̃‖²_{S₂}=Σλ²` | `HilbertSchmidtBridge.lean`: `hilbertSchmidtSq`, `hilbertSchmidtSq_eq_spectralMass`, `card_badEigenvalues_quarter_le_hilbertSchmidt` | **[LEAN]**。 |
| `13:25-35`：构造 good space 并记账 codimension | `Ṽ_good=(S_E+S_R)⊥=ker E ∩ spectralGood`，`codim≤r+16c₀⁻²s` | `SubspaceBudget.lean`: `codim_inf_le`；`SpectralGoodSpace.lean`: `hermitianGoodSpace`, `codim_hermitianGoodSpace_quarter_le_hilbertSchmidt`；`WhitenedMinMax.lean`: `whitenedGoodSpace`, `codim_whitenedGoodSpace_le_rank_add_hilbertSchmidt` | **[LEAN]**，常数 `16` 在声明类型中显式出现。 |
| `13:33-35`：在 good space 上下界 | `P̃+Ẽ+R̃ ⪪c c₀I-c₀I/4=3c₀I/4` | `DiagonalRemainder.lean`: `diagonalQuadratic_lower_on_coordinateGoodSpace`；`WhitenedMinMax.lean`: `remainder_lower_on_hermitianGoodSpace`, `three_quarters_lower_on_whitenedGoodSpace`, `three_quarters_lower_on_physicalGoodSpace` | **[LEAN]**，常数 `3*c₀/4` 显式保留。 |
| `13:36-46`：由正性空间控制负惯性，再加 ambient codimension `d` | `n₋(A↾V)≤r+16c₀⁻²s`，ambient 版再加 `d` | `NegativeIndex.lean`: 自然数版 `NegativeIndexLE`；`RealNegativeIndex.lean`: 实数 budget 版 `NegativeIndexBound`；`rank_plus_hilbertSchmidt_minmax` 与 `...after_linearEquiv` 给出纸面主界 | **[LEAN]**。ambient `+d` 由通用 subspace/codimension 引理组装，尚未与 M09 的实际 retained space 绑定。 |

### 3.2 M01 假设对照结论

- Lean 并未把待证结论改写为假设：秩界、谱阈值记账、HS 恒等式、
  good-space 下界和负指数界都是已证定理。
- `hdecomp`, `hP`, `hEzero`, `hRdiag`, `hGcoord` 是把纸面中“白化后恰为这些
  对象”展开成可检查接口；它们不是 M01 gap，但必须在 M08--M10 的具体
  应用中由主模型、edge 和 remainder 证书构造。
- **尚存 gap**：将 M09 retained space 及 M06--M08 的具体 `P,E,R,G` 组装到
  `rank_plus_hilbertSchmidt_minmax_after_linearEquiv`；这是节点集成 gap，不是 M01 线性代数 gap。

## 4. M02 详译：Hardy gauge 与不变 contour form

**来源**：`sections/01_invariant_contour.tex:1-199`，`sec:common-matrix`。
**去向**：`ZetaZero.HardyGaugeInvariantContourForm`。
**当前验收声明**：`exists_packetSameForm_zeroSum`（条件是边界无 `Z₁` 零点）。
**本阶段证据命令**：`lake build ZetaZero.HardyGaugeInvariantContourForm` （PASS）。

### 4.1 段落 / 公式 / 声明映射

| 论文位置与意图 | 公式、量词与隐含条件 | Lean 接口与假设对照 | 状态 / gap |
|---|---|---|---|
| `01:4-18`：固定 `c=2`，在 `-1≤σ≤2`, `T₁≤t≤T₂` 的对称高矩形选择分支 | `T₁<T₂`，水平边界避免相关零/极点；开邻域单连通且不触及实轴 | `HighRectangle.lean`: `highRectangleNhd` 及单连通/虚部非零性质；`HolomorphicSquareRoot.lean`: `exists_hardyGaugeSquareRoot` 在 `IsSimplyConnected`, `IsOpen`, `im≠0` 下构造 `q` 并证 `q z ^ 2 = chiOneSub z` | **[LEAN]** 局部分支存在性。**[GAP]** 论文中由 M03 good-height 命题生成的具体 `T₁,T₂` 尚未构造。 |
| `01:19-45`：定义 `q†(s)=overline(q(1-conj s))` 并得 Hardy 反射 | `q†=q⁻¹`；`𝒵(1-conj s)=conj(𝒵(s))`；分支解析且非零 | `BranchReflection.lean`: `hardyReflect`, `branchDagger`, `hardyGauge`, `branchDagger_eq_inv_on_highRectangle`, `hardyGauge_reflection_on_highRectangle` | **[LEAN]**；实际假设是 `hε>0`, `T₁<T₂`, `ε<T₁`, `q` 解析及全局平方恒等式。 |
| `01:46-56`：定义 `f=-½ χ'/χ`, `Z₁=ζ'+fζ` 并识别 stationary source | `q'/q=f`，`𝒵'=qZ₁`；`q≠0` 使 `𝒵` 与 `ζ` 零点相同 | `GaugeDerivative.lean`: `hardyF`, `zetaOne`, `deriv_branch_eq_hardyF_mul`, `deriv_hardyGauge_eq_branch_mul_zetaOne`, `hardyGauge_eq_zero_iff_zeta_eq_zero`；`ZetaOneAnalytic.lean` 给出高矩形上解析性 | **[LEAN]**；零点重数的局部输送主要经 `Zeta23HardyBridge` 的 germ 恒等式实现。 |
| `01:58-73`：由对称 shift 产生曲率 | `C_𝒵=𝒵𝒵''-(𝒵')²=½∂²_a[𝒵(s+a)𝒵(s-a)]` 在 `a=0` 处的值；`p=La` 引入正归一化 `L⁻²` | `CurvatureAlgebra.lean`: `curvatureJet`；`SymmetricShiftCurvature.lean`: `half_deriv2_symmetricShiftProduct_eq_curvature`, `hardyGauge_half_deriv2_symmetricShift_eq_curvature`；`ZetaCurvature.lean`: `hardyGauge_curvature_source_on_highRectangle` | **[LEAN]** 未归一化曲率代数。**[GAP]** `p=La` 及整个 contour matrix 的统一 `L⁻²` 类型化尚未包装为一个 paper-facing 定义。 |
| `01:75-101`：定义 packet 极化 `ℼ_{v,w}` | `B_v=Σvνψν`，`B_v#(z)=conj(B_v(conj z))`，`z(s)=-i(s-1/2)`，`ℼ_{v,w}=B_w(z(s))B_v#(z(s))`；有限指标集，packet entire | `PacketPolarization.lean`: `packetSum`, `sharp`, `contourCoordinate`, `contourCoordinate_hardyReflect`, `sharp_conj`, `packetPolarization`, `packetPolarization_hardyReflect_swap`, `differentiable_packetPolarization` | **[LEAN]**；Lean 明确要求 `[Fintype ι]`。反射交换恒等式已通过本轮添加的 acceptance theorem；实际 contour form 的反向还未包装。 |
| `01:102-120`：同一 contour form 从 `𝒵''/𝒵'` 替换为 `Z₁'/Z₁` | `𝒵''/𝒵'=f+Z₁'/Z₁`；`f C ℼ` 解析，围道积分为零 | `SameFormLogDerivative.lean`: `logDeriv_hardyGauge_deriv_eq`；`ContourCancellation.lean`: `rectangleBoundaryIntegral_eq_zero_of_analyticOnNhd`；`SameFormContour.lean` 的 correction 解析性；`PacketSameForm.lean`: `packetSameForm_boundaryIntegral_eq` | **[LEAN]** 边界积分等式。假设显式包含 `NonzeroOnRectangleBoundary zetaOne` 与边界可积性；`PacketBoundaryIntegrability.lean` 在边界非零时提供对应可积性。 |
| `01:121-151`：去掉全纯全微分项并直线化为 zero kernel | `(𝒵''/𝒵')C = L⁻²(𝒵𝒵''²/𝒵' - 𝒵'𝒵'')`；`s=1/2+iz`，`𝒵'=-iF'`, `𝒵''=-F''`, `ds=i dz` | `SameFormContour.lean` 证明 Hardy 与 `Z₁` 边界形式之差为解析 correction；M03 `StraighteningBridge.lean` 证导数换元 | **[LEAN]+[GAP]** 两端部件已证；包含方向、`L⁻²` 和 packet product 的完整 contour change-of-variables 尚无单一验收定理。 |
| `01:153-171`：定义 Hermitian matrix `A_T` 并区分 reference Gram `𝔊_T` | `⟨A_Tv,w⟩=ℰ_T(v,w)`，需反射、边界方向及 packet 次序共同给出 sesquilinearity/Hermitian | 当前 facade 有 scalar/packet boundary identity 与反射律，但没有定义有限矩阵 `A_T` 并证 `IsHermitian` 的验收声明 | **[GAP M02-HERMITIAN-MATRIX]**：需要显式的反向 contour/adjoint 证明，不能用标量重写代替。 |
| `01:175-199`, `lem:allowed`：列出后续允许的四类变换 | congruence；限制到 codim `d`；rank-`r` 扰动；相对 `S₂` remainder | M01 `CongruenceTransport`, `SubspaceBudget`, `FiniteRankPerturbation`, `WhitenedMinMax` 分别形式化这些线性代数原理 | **[LEAN]** 通用代数原理；将 M02 的具体 `A_T` 接入这些原理仍属后续集成。 |
| `prop:same-form-identity` 内部零点和 | contour 避开 `Z₁=0`，矩形内零点有限，按 `analyticOrderNatAt` 计重数 | `PacketZeroSum.lean`: `packetSameForm_zeroSum` 以给定有限零集 `Z`为输入；`exists_packetSameForm_zeroSum` 构造 `Z`；核心依赖 `Analytic.RectangleArgumentPrinciple.rectangleWeightedArgumentPrinciple` | **[LEAN]** 有限重数加权 `Z₁` zero sum。**[GAP]** 尚未特化成 M03 stationary block weights。 |
| normalization bridge | 论文 `f`/`Z₁` 需与外部 Zeta23 的 `L₂`/`hardyW` 一致 | `Zeta23HardyBridge.lean`: `hardyF_eq_zeta23_L2`, `zetaOne_eq_zeta23_hardyW`, derivative/order/zerohood transport，假设 `s.im ≠ 0` | **[LEAN]**；这是外部实现的定向 bridge，不等于导入 Zeta23 整个证明路线。 |

### 4.2 M02 明确 gap

1. **M02-GOOD-BOUNDARY**：从 M03 局部零点计数/对数导数界构造具体
   `T₁∈[T,T+1]`, `T₂∈[2T,2T+1]` 及 `NonzeroOnRectangleBoundary zetaOne`。
2. **M02-STATIONARY-SPECIALIZATION**：把 `exists_packetSameForm_zeroSum` 中的
   `analyticOrderNatAt zetaOne ρ * hardyCurvature q ρ * packetPolarization ... ρ`
   特化为 M03 的简单 stationary residue scalar/共轭块。
3. **M02-HERMITIAN-MATRIX**：定义有限 packet matrix，对全边界证明
   `A(w,v)=conj(A(v,w))`，并保留反射、方向反转和 adjoint。
4. **M02-NORMALIZATION-ASSEMBLY**：将 `L⁻²`、`p=La` 和 straightening Jacobian 整合为
   `prop:same-form-identity` 的单一 paper-facing Lean 定理。

## 5. M03 详译：零点侧 stationary geometry

**来源**：`sections/02_zero_side.tex:1-501`，`sec:zero-side`。
**去向**：`ZetaZero.ZeroSideStationaryGeometry`。
**当前验收声明**：局部链以
`tendsto_stationaryKernel_principalCoefficient`,
`conjugatePair_negativeIndexLE_one`,
`conjugatePair_exists_negativeDirection`,
`straighten_hardyGauge_simpleStationary_iff_zetaOne_simpleZero` 为终端；
全局 `n_-(A_H)=B(H)+P(H')` 尚未形式化。
**本阶段证据命令**：`lake build ZetaZero.ZeroSideStationaryGeometry` （PASS）。

### 5.1 段落 / 公式 / 声明映射

| 论文位置与意图 | 公式、量词与隐含条件 | Lean 接口与假设对照 | 状态 / gap |
|---|---|---|---|
| `02:1-28`：用 `s=1/2+iz` 直线化临界线 | `F(z)=𝒵(1/2+iz)`，`Ω_T` 关于 `z↦conj z` 不变，`F(conj z)=conj(F z)`；zero kernel 为 `-L⁻² F(F'')²/F'` | `StraighteningBridge.lean`: `spectralOfZeroCoordinate`, `straighten`, 两个坐标互逆 simp 引理，`deriv_straighten`, `secondDeriv_straighten`, `straighten_hardyGauge_conj`, `straighten_hardyGauge_real_conj` | **[LEAN]** 坐标、一/二阶导数和反射字典。**[GAP]** 带边界方向及 `L⁻²` 的整体 contour 换元。 |
| `02:31-62`, `lem:stationary-blocks`：简单 stationary zero 的 residue | `H'(c)=0`, `H''(c)≠0`，residue `-L⁻²H(c)H''(c)` | `StationaryResidueAnalytic.lean`: `stationaryKernel`, `stationaryKernel_eq_logDeriv_mul`, `tendsto_stationaryKernel_principalCoefficient`；假设 `AnalyticAt ℂ H c`, `deriv H c=0`, `deriv (deriv H) c≠0` | **[LEAN]** punctured-neighbourhood 主系数极限。它是 residue 证据，但未与全局 contour sum 组装。 |
| `02:39-47`：实 stationary point 的符号 | `L>0`, `H(c)H''(c)>0 ⇒ -H(c)H''(c)/L²<0` | `StationaryResidueBlocks.lean`: `realStationaryWeight`, `realStationaryWeight_neg` | **[LEAN]**。 |
| `02:43-61`：非实共轭对形成 `2×2` Hermitian block | `[[0,conj w],[w,0]]`，`w≠0`，特征值 `±‖w‖`，恰有一个负方向 | `StationaryResidueBlocks.lean`: `conjugatePairBlock_isHermitian`, `det_conjugatePairBlock`, `conjugatePairQuadratic_negativeVector_neg`；`StationaryBlockInertia.lean`: `conjugatePair_negativeIndexLE_one` 与 `conjugatePair_exists_negativeDirection` | **[LEAN]**：“至多一个负维数 + 存在负方向”给出局部 exact-one 结论。 |
| `02:65-99`：定义 bandwidth reserve 和 packet | `L_pkt=L+C_pkt log L`；`φ_L` 平顶、紧支撑；`ψ_L` 为 Fourier transform；固定 strip 上快速衰减 | 当前 `PacketPolarization.lean` 只接收抽象 entire packet family，没有 `φ_L`, `ψ_L`, support/bandwidth/decay 定义 | **[GAP M03-PACKET-CONSTRUCTION]**。 |
| `02:100-129`, `lem:evaluation-rank`：局部移动使 evaluation 满射 | 对任意互异 stationary nodes 及非空开 centre intervals，存在 `τ_j` 使 evaluation determinant 非零 | 无对应 Lean 定理；需 Fourier uniqueness + exponential-polynomial/Vandermonde + real-analytic determinant 非恒零 | **[PAPER]/[GAP M03-EVALUATION]**。这是全局 pullback 惯性等式的关键缺口。 |
| `02:130-170`, `lem:packet-riesz`：近格点 packet 的 Riesz 界 | `2πΣ‖c_j‖² ≤ ‖Σc_jψ_{L,τ_j}‖² ≤ 6πΣ‖c_j‖²`，centre 扰动最多 `T⁻¹⁰⁰` | 无对应 Lean packet synthesis/norm 定理 | **[PAPER]/[GAP M03-RIESZ]**。 |
| `02:171-217`, `lem:packet-dimension`：用 `C_pkt T log L` 余量覆盖 stationary zeros 和 terminal collars | `d_T=T L/(2π)+C_pkt T log L/(2π)+O(L)`；需 Riemann--von Mangoldt 与 `N(F')-N(F)=polylog` | Lean 已有 `dyadicN`/`NcountZetaOne` 等定义和 Zeta23 count bridge，但没有该 asymptotic/dimension 定理 | **[PAPER]/[GAP M03-DIMENSION]**；且依赖下方 good-height gap。 |
| `02:218-254`, `lem:coordinate-restriction`：坐标删除保持 Riesz/rank/HS 界 | `A↦P_JAP_J*`, `G↦P_JGP_J*`；rank 不增，absolute HS 不增，relative HS 需重跑 analysis-map criterion | M01/M08 有通用 codimension/rank 工具，但没有将 packet coordinate compression 与 reference map `W_J` 统一的定理 | **[PAPER]/[GAP M03-COMPRESSION]**。 |
| `02:255-276`, `lem:horizontal-decay`：删除端点 collar 使水平 connector 快速衰减 | 删除 `O(T)=o(N_T)` 方向；任意固定阶曲率导数为 `O_A(T^{-A})` | 无对应 packet decay + zeta/source-growth 组合定理 | **[PAPER]/[GAP M03-HORIZONTAL]**。 |
| `02:278-293`：全局 residue pullback 与惯性等式 | `A_H=E_H*W_HE_H`，`E_H` 满射，因而 `n_-(A_H)=B(H)+P(H')` | `EvaluationPullback.lean`: `evaluationPullback`, `NegativeIndexWitness`, `evaluationPullback_strictlyNegativeOn_map`, `evaluationPullback_domRestrict_injective`, `evaluationPullback_negativeIndexLE`, `evaluationPullback_negativeWitness_of_surjective`, `evaluationPullback_negativeIndex_certificate` 现在给出上界以及显式满射条件下的 witness 下界；尚无 finite node 之间的满射 bridge、直和 block operator、contour residue 装配与 exact `B+P` 合成 | **[LEAN]+[GAP M03-GLOBAL-INERTIA]**。`q 0 = 0` 与 `NegativeIndexWitness` 是明确条件，不是隐藏假设。 |
| `02:294-324`, `lem:real-bookkeeping`：实零点/驻点记账 | `R(H')=R(H)+2B(H)+O(1)`，要求实解析且零点、stationary points 简单 | 无 Rolle/alternation 的有限计数 Lean 接口 | **[PAPER]/[GAP M03-REAL-BOOKKEEPING]**。 |
| `02:326-363`, `lem:local-z1-count`：固定圆盘 Jensen 计数 | `N_{Z₁}([U,U+1])+N_ζ([U,U+1]) ≪ log U`，`U≍T` | `Analytic/JensenZeroCount.lean` 有抽象 `jensen_divisor_bound*`，但未被 M03 facade import，也未对 `ζ,Z₁` 构造多项式增长/中心下界 | **[EXPERIMENT]/[GAP M03-JENSEN-SPECIALIZATION]**。 |
| `02:364-418`, `lem:local-log-derivative`：局部 Hadamard/Jensen 因子化 | `F₀'/F₀=Σ(s-ρ)⁻¹+O((log T)^{C₀})`，`F₀∈{ζ,Z₁}`，离零点且在固定内圆盘 | 无对应 specialized factorization/Borel--Carathéodory 声明 | **[PAPER]/[GAP M03-LOGDERIV]**。 |
| `02:419-496`, `prop:z1-zeta-decrement`：同时好高度与计数差 | 存在 `T₁,T₂`，边界避免 `R=Z₁/ζ` 的零/极点；`N(Z₁)-N(ζ)=O(polylog)=o(N_T)` | `Analytic/GoodHeightCombinatorics.lean`: 抽象 `exists_far_point` 但未 import；`ZetaOneCounting.lean`: `NcountZetaOne_eq_NcountW`, `zetaOneZerosInStrip_holds`；不存在论文该 proposition 的 Lean 版 | **[EXPERIMENT]/[GAP M03-GOOD-HEIGHT]**。 |
| 零点反射与重数 | `ρ↦1-conj ρ`，离开临界线时无不动点，重数保持 | `Analytic/ZetaReflection.lean`, `ReflectionPairing.lean`, `OffCriticalPairing.lean`: `reflectZetaZero`, `offCritical_reflection_pair`, `reflectOffCriticalEquiv`, `zetaZeroMultiplicity_reflectOffCriticalEquiv` | **[LEAN]** zeta 零点集的反射配对。 |
| Hardy/Zeta23 stationary 字典 | 临界线 `Z₁=0` 等价于 real Hardy `Z'=0`；简单性对应 | `StationaryDictionary.lean`: `zetaOne_criticalLine_eq_zero_iff_stationary`, `zetaOne_simpleZero_criticalLine_iff_simpleStationary`；`StraighteningBridge.lean`: complex straightened 版 `...eq_zero_iff...`, `...simpleStationary_iff...` | **[LEAN]**，需 `t≠0` 或高矩形假设。 |

### 5.2 M03 最短后续定理链

1. 将 `φ_L/ψ_L` 及 finite packet synthesis 定义稳定化，以
   `evaluation-map surjective + Riesz bounds` 为一个验收接口，不分散报告单个辅助引理。
2. 用已验证的 `exists_packetSameForm_zeroSum` 和
   `tendsto_stationaryKernel_principalCoefficient` 组装 finite block pullback。
3. 用 evaluation surjectivity + block inertia 证明 paper-facing
   `n_-(A_H)=B(H)+P(H')`。
4. 独立完成 Jensen specialization → local log derivative → simultaneous good height →
   `N(Z₁)-N(ζ)=o(N_T)`；然后反向提供 M02 的边界非零证书。

## 6. 验证基线与故障记录

### 6.1 本阶段命令

文档中 **[LEAN]** 的第一层证据是以下稳定 facade：

```bash
lake build ZetaZero.FiniteDimensionalInertiaReduction
lake build ZetaZero.HardyGaugeInvariantContourForm
lake build ZetaZero.ZeroSideStationaryGeometry
```

完成文档后的集成验收命令为：

```bash
npm test -- lean-all
python3 scripts/check_lean_placeholders.py
npm test -- blueprint-decls
python3 -m pytest -q
```

### 6.2 结果记录（2026-08-21）

| 命令 | 当前观测 | 允许得出的结论 |
|---|---|---|
| `lake build ZetaZero.FiniteDimensionalInertiaReduction` | PASS，`Build completed successfully` | M01 facade 及其 import 闭包可构建。 |
| `lake build ZetaZero.HardyGaugeInvariantContourForm` | PASS，`Build completed successfully` | M02 facade 及选定 Zeta23 bridge 可构建。 |
| `lake build ZetaZero.ZeroSideStationaryGeometry` | PASS，`Build completed successfully`；外部 `Zeta23/.../ZFunction.lean` 有 linter/deprecation warnings | M03 facade 可构建；警告来自外部参考树，不改变构建成功的事实。 |
| `npm test -- lean-all` | PASS，`1 passed` | 全部 `ZetaZero/**/*.lean` source 在 all-source gate 中可构建；不代表节点 green。 |
| `python3 scripts/check_lean_placeholders.py` | PASS，`scanned 119 Lean source files` | 只检查禁用 placeholder/项目 axiom 类模式，不证明数学路线完整。 |
| `npm test -- blueprint-decls` | PASS，`1 passed` | Blueprint 引用的声明可解析；green 还需 statement/proof `\leanok` 和 `leanblueprint all`。 |
| `python3 -m pytest -q` | **FAIL (runner CLI)**，`unknown test selector(s): -q` | 本库自定义 `pytest/__main__.py` 把 `-q` 解析为 selector；这是验收命令与 runner CLI 不匹配，不是 Lean 定理失败。 |
| `python3 -m pytest` | PASS，`14 passed` | 当前自定义 runner 支持的全部定向门禁通过。 |

当前没有任何 major node 可仅根据上述 facade build 称为 green。green 必须同时
满足 `doc/status.md` 和项目政策中的 Lean、placeholder、Blueprint declarations、
statement/proof `\leanok` 及完整 `leanblueprint all` 条件。

### 6.3 失败记录模板

```text
date / commit:
major node:
paper label and formula:
target facade / declaration:
command:
exit code:
minimal diagnostic:
classification: compile | type mismatch | missing mathematical hypothesis |
                missing import | stale external reference | blueprint
parity: VERIFIED | BROKEN | UNVERIFIED
next theorem-sized action:
```

## 7. 扩展规则

M04--M10 的后续详译直接复用本文的三级表格和状态标记，不重新设计
格式。每次扩展必须先锁定 paper label、major node、依赖、稳定 facade 和一个
acceptance theorem，再把“论文声称 / Lean 已证 / 条件接口 / gap”逐项分开。
