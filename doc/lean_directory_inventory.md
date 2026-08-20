# `ZetaZero/` 目录与声明职责清单

> 快照日期：2026-08-21
> 范围：工作树中全部 119 个 `ZetaZero/**/*.lean` 文件。
> 主索引：[`main_tex_to_lean_system.md`](main_tex_to_lean_system.md)。

## 1. 读取规则

- **稳定 facade** 是 `doc/roadmap.md` 列出的 M01--M10 根模块。子模块可改名，
  facade 路径不应随意改动。
- **facade 覆盖**中的“是”表示文件在对应稳定 facade 的当前 import 闭包中；
  “否”表示只有 source 或兼容/实验 import path，不能由稳定 facade 构建推断其状态。
- **主要声明**只列验收或导航用标识符，不是完整 `#check` 清单。
- **source 可构建**和**数学节点完成**是两件事。即使 `lean-all` 成功，
  未与论文假设和验收定理闭合的目录仍只是 abstract foundation 或 experiment。

## 2. 目录级职责、依赖和边界

| 目录 | 数学职责 | 节点 | 上游 | 下游 | 稳定 facade / 当前状态 |
|---|---|---|---|---|---|
| `ZetaZero/` | 稳定 public import roots | M01--M10 | 各子目录 | 用户与 Blueprint | 十个 M facade；没有 major node green |
| `Analytic/` | zeta/完成 zeta、反射、零点集、计数、Jensen 和 rectangle argument principle 的共享基础 | 主要 M02--M03，并供 M10 计数 | Mathlib，选定 Zeta23 模块 | M02, M03, M10 及后续节点 | 无独立稳定 facade；按实际 importer 进入 M02/M03；`GoodHeightCombinatorics`/`JensenZeroCount` 尚未进入 facade |
| `FiniteDimensionalInertiaReduction/` | codimension、负指数、有限秩删除、谱阈值、HS 恒等式、good space、白化与回传 | M01 | Mathlib | M10，也被 M03/M08/M09 工具层使用 | `ZetaZero.FiniteDimensionalInertiaReduction`；Lean core complete, Blueprint pending |
| `HardyGaugeInvariantContourForm/` | high rectangle、平方根分支、Hardy 反射、`Z₁`、曲率、packet 极化、same-form contour 和 zero sum | M02 | `Analytic/`, Mathlib, 选定 Zeta23 | M03, M04 以及全部 arithmetic 下游 | `ZetaZero.HardyGaugeInvariantContourForm`；contour/zero-sum core verified，全局 stationary specialization 缺失 |
| `ZeroSideStationaryGeometry/` | straightening、stationary residue、实 scalar/共轭 pair block惯性、Hardy/Zeta23 字典 | M03 | M02, `Analytic/`, M01 负指数工具 | M08, M10 | `ZetaZero.ZeroSideStationaryGeometry`；局部链 verified，packet surjectivity/good heights 缺失 |
| `RightEdgeArithmeticSource/` | exact/model/residual source algebra，curvature coefficient，stationary phase/Fresnel 有限窗口控制 | M04 | M02, Mathlib | M05 | `ZetaZero.RightEdgeArithmeticSource`；有限窗口定量核心存在，packet/Perron transfer 缺失 |
| `HLPLocalModel/` | Mangoldt/HLP 系数层级、卷积递推、加权均方、factorial carrier、resolvent/Laurent 接口 | M05 | M04, Mathlib, 选定 Zeta23 | M06, M07 | `ZetaZero.HLPLocalModel`；algebra/carrier foundations verified，实际 local replacement 缺失 |
| `GlobalModelSpectralFloor/` | cusp-minus-regular/Schur 下界的抽象证书 | M06 | M05 | M08 | `ZetaZero.GlobalModelSpectralFloor`；abstract foundation，非论文具体 model floor |
| `DivisorGramArithmeticTransfer/` | finite positive Gram、gcd/totient Hilbert Gram 和 operator-valued lift | M07 | M05, Mathlib | M08 | `ZetaZero.DivisorGramArithmeticTransfer`；abstract/concrete gcd identities 存在，定量 arithmetic transfer 缺失 |
| `FrameCompression/` | finite-feature、fixed-edge range 与 translated-pole jet 秩记账 | M08 | M03, M06, M07, M01 工具 | M09 | `ZetaZero.FrameCompression`；rank foundation only |
| `RetainedSpace/` | kernel 交的 codimension 预算 | M09 | M08, M01 | M10 | `ZetaZero.RetainedSpace`；abstract bookkeeping only |
| `GenericPerturbationMinMaxEndgame/` | relative perturbation、扰动后 min--max、密度一比值归一化 | M10 | M01, M03, M09, `Analytic/` | 最终 theorem | `ZetaZero.GenericPerturbationMinMaxEndgame`；conditional endgame interface，分析 little-o 输入缺失 |

## 3. `ZetaZero/` 根 facade 文件

| 文件 | 职责 / import 边界 | 公开声明 | 状态 |
|---|---|---|---|
| `FiniteDimensionalInertiaReduction.lean` | M01，导入 `WhitenedMinMax` 闭包 | facade 本身无新声明 | 稳定；当前 facade build PASS |
| `HardyGaugeInvariantContourForm.lean` | M02，显式导入 curvature/contour/packet/zero-sum/bridge 链 | facade 本身无新声明 | 稳定；当前 facade build PASS |
| `ZeroSideStationaryGeometry.lean` | M03，导入 M02、零点计数/反射及 stationary 链 | facade 本身无新声明 | 稳定；当前 facade build PASS |
| `RightEdgeArithmeticSource.lean` | M04，导入 M02 与 source/stationary 子模块 | facade 本身无新声明 | 稳定；节点进行中 |
| `HLPLocalModel.lean` | M05，导入 M04 与 HLP 子链 | facade 本身无新声明 | 稳定；节点进行中 |
| `GlobalModelSpectralFloor.lean` | M06，导入 M05 和 `PrimitiveSchurFloor` | facade 本身无新声明 | 稳定；abstract foundation |
| `DivisorGramArithmeticTransfer.lean` | M07，导入 M05 和 Gram/gcd 子模块 | facade 本身无新声明 | 稳定；abstract foundation |
| `FrameCompression.lean` | M08，导入 M03/M06/M07 与 feature/fixed-edge-rank 子模块 | facade 本身无新声明 | 稳定；主分析链未完成 |
| `RetainedSpace.lean` | M09，导入 M08 和 kernel budget | facade 本身无新声明 | 稳定；abstract bookkeeping |
| `GenericPerturbationMinMaxEndgame.lean` | M10，导入 M01/M03/M09 与 perturbation/density 链 | facade 本身无新声明 | 稳定；conditional endgame |

## 4. `Analytic/` 文件清单

| 文件 | 职责 | 主要声明 | 稳定 facade 覆盖 |
|---|---|---|---|
| `CompletedZeta.lean` | 完成 zeta/Gamma 解析性和对数导数 | `analyticAt_riemannZeta`, `logDeriv_completedZeta`, `completedZeta_zeros_strip` | 是，经 M02 |
| `FunctionalEquationFactor.lean` | `chiFE`, `chiOneSub` 与 functional equation factor 的解析/非零/共轭性 | `chiFE_mul_chiFE_one_sub`, `riemannZeta_one_sub_eq_chiOneSub_mul_of_strip`, `chiOneSub_ne_zero_on_criticalStrip` | 是，经 M02 |
| `GoodHeightCombinatorics.lean` | 有限禁区中选取远点的组合引理 | `exists_far_point` | **否**；M03 good-height 候选工具 |
| `JensenZeroCount.lean` | 抽象 Jensen divisor 计数界 | `jensen_divisor_bound`, `jensen_divisor_bound_of_center_lower`, `jensen_divisor_bound_of_polynomial_growth` | **否**；未特化到 `ζ,Z₁` |
| `OffCriticalPairing.lean` | 离开临界线零点的无不动点反射等价 | `offCriticalZetaZerosIn`, `reflectOffCriticalEquiv`, `zetaZeroMultiplicity_reflectOffCriticalEquiv` | 是，M03 |
| `RectangleArgumentPrinciple.lean` | 包装 vendored 加权矩形 argument principle | `rectangleWeightedArgumentPrinciple` | 是，M02 |
| `ReflectionPairing.lean` | zeta 零点反射、临界线不动点判定和重数配对 | `reflectZetaZero_eq_self_iff`, `offCritical_reflection_pair` | 是，M03 |
| `ZeroCountRelations.lean` | `N`, `N₀`, distinct/simple/dyadic 计数间单调关系 | `zero_count_chain`, `dyadicN0_le_dyadicN`, `N0simple_dyadic_le_dyadicN0` | 是，M03/M10 |
| `ZeroCounting.lean` | 非平凡 zeta 零点、重数和窗口计数的基本定义 | `IsNontrivialZetaZero`, `zetaZeroMultiplicity`, `Ncount`, `dyadicN`, `dyadicN0` | 是，M03 |
| `ZeroFiniteness.lean` | zeta 零点局部有限与 window finiteness | `analyticOrderAt_riemannZeta_ne_top`, `riemannZeta_zeros_locallyFinite`, `zetaZerosIn_finite` | 是，M03 |
| `ZetaOneCounting.lean` | `Z₁` 零点集/重数/计数与 Zeta23 `hardyW` 对接 | `NcountZetaOne_eq_NcountW`, `zetaOneZerosInStrip_holds` | 是，M03 |
| `ZetaReflection.lean` | `ρ↦1-conj ρ` 反射和解析阶数传输 | `reflectZetaZero`, `reflectZetaZero_mem`, `zetaZeroMultiplicity_reflect` | 是，经 M02/M03 |

## 5. `FiniteDimensionalInertiaReduction/` 文件清单（M01）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `Basic.lean` | codimension 和二次型符号谓词 | `codim`, `NonnegativeOn`, `StrictlyNegativeOn` | 是 |
| `SubspaceBudget.lean` | 子空间交的 codim 界与正/负空间不交 | `codim_inf_le`, `finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn` | 是 |
| `FiniteRankPerturbation.lean` | 线性映射核的 codim=值域秩 | `codim_ker_eq_finrank_range`, `codim_ker_le` | 是 |
| `NegativeIndex.lean` | 自然数值 negative-index 上界 | `NegativeIndexLE`, `negativeIndexLE_codim_of_nonnegativeOn` | 是 |
| `RealNegativeIndex.lean` | 实数 budget 版 negative-index 上界 | `NegativeIndexBound`, `negativeIndexBound_of_nonnegativeOn_of_codim_le` | 是 |
| `RankPlusGoodSpace.lean` | finite-rank kernel 与 good space 的合并惯性界 | `negativeIndexBound_rank_plus_goodSpace` | 是 |
| `SpectralThresholdCount.lean` | 标量序列的阈值计数 | `thresholdSet`, `card_thresholdSet_mul_sq_le_sum_sq` | 是 |
| `CoordinateGoodSpace.lean` | 坐标坏方向映射与 kernel good space | `badCoordinateMap`, `coordinateGoodSpace`, `codim_coordinateGoodSpace_le` | 是 |
| `DiagonalRemainder.lean` | 对角 remainder 二次型在 good space 上的下界 | `diagonalQuadratic`, `diagonalQuadratic_lower_on_coordinateGoodSpace` | 是 |
| `HermitianThreshold.lean` | Hermitian 特征值的 spectral mass 和坏特征值数 | `spectralMass`, `card_badEigenvalues_quarter_le_sixteen` | 是 |
| `HilbertSchmidtBridge.lean` | matrix trace HS 平方与 spectral mass 恒等式 | `hilbertSchmidtSq`, `hilbertSchmidtSq_eq_spectralMass`, `card_badEigenvalues_quarter_le_hilbertSchmidt` | 是 |
| `SpectralGoodSpace.lean` | Hermitian eigenbasis 下的显式 good space 及 codim 界 | `hermitianGoodSpace`, `codim_hermitianGoodSpace_quarter_le_hilbertSchmidt` | 是 |
| `MinMaxAssembly.lean` | rank + remainder good-space 下界与 negative-index 组装 | `three_quarters_lower_bound_on_good_space`, `negativeIndexBound_rank_plus_hilbertSchmidt_budget` | 是 |
| `CongruenceTransport.lean` | 线性等价下二次型、codim 和负惯性回传 | `pullbackForm`, `negativeIndexBound_pullback`, `lower_bound_on_transportedSubspace` | 是 |
| `WhitenedMinMax.lean` | 白化/物理坐标的 paper-facing M01 终端 | `codim_whitenedGoodSpace_le_rank_add_hilbertSchmidt`, `three_quarters_lower_on_physicalGoodSpace`, `rank_plus_hilbertSchmidt_minmax_after_linearEquiv` | 是，facade 终点 |
| `FiniteFeatureRank.lean` | 早期 finite-feature kernel budget 工具 | `finiteFeature_kernel_budget`, `twoFiniteFeature_kernel_budget` | **否**；稳定同类 API 在 M08 `FrameCompression/FiniteFeatureRank.lean` |

## 6. `HardyGaugeInvariantContourForm/` 文件清单（M02）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `HighRectangle.lean` | high rectangle 开邻域、凸/单连通、虚部非零 | `highRectangleNhd`, `isSimplyConnected_highRectangleNhd`, `highRectangleNhd_im_ne_zero` | 是 |
| `HolomorphicSquareRoot.lean` | 非零解析函数及 `chiOneSub` 的全局解析平方根 | `exists_analyticOnNhd_squareRoot`, `exists_hardyGaugeSquareRoot` | 是，经 `BranchReflection` |
| `CriticalLinePhase.lean` | 临界线参数、Gamma phase carrier 和分支基点 | `criticalLine`, `criticalPhase`, `criticalPhase_sq`, `conj_branch_eq_inv_on_criticalLine` | 是，经 `BranchReflection` |
| `BranchReflection.lean` | Hardy reflection、分支 dagger、Hardy gauge 及反射律 | `hardyReflect`, `hardyGauge`, `branchDagger_eq_inv_on_highRectangle`, `hardyGauge_reflection_on_highRectangle` | 是 |
| `GaugeDerivative.lean` | `f`/`Z₁` 定义和 `𝒵'=qZ₁` | `hardyF`, `zetaOne`, `deriv_hardyGauge_eq_branch_mul_zetaOne`, `hardyGauge_eq_zero_iff_zeta_eq_zero` | 是 |
| `GaugeSecondDerivative.lean` | 平方根分支二阶导数恒等式 | `deriv2_branch_eq_hardyF`, `deriv2_branch_eq_hardyF_on_highRectangle` | 是 |
| `CurvatureAlgebra.lean` | 抽象 jet 乘法和 curvature factorization | `curvatureJet`, `symmetricShiftSecondJet`, `curvatureJet_mul_factorization` | 是 |
| `CurvatureDerivativeBridge.lean` | jet 代数与 Lean `deriv` 二阶导数对接 | `deriv2_mul_eq_mulSecondJet`, `curvature_deriv_mul_factorization` | 是 |
| `ZetaCurvature.lean` | Hardy gauge curvature 到 zeta/phase source 的解析分解 | `hardyGauge_curvature_source`, `hardyGauge_curvature_source_on_highRectangle` | 是 |
| `SymmetricShiftCurvature.lean` | 对称 shift 二阶导数生成 curvature | `half_deriv2_symmetricShiftProduct_eq_curvature`, `hardyGauge_half_deriv2_symmetricShift_eq_curvature` | 是 |
| `SameFormLogDerivative.lean` | `𝒵''/𝒵'=f+Z₁'/Z₁` 型恒等式 | `hardyGauge_second_over_first_eq`, `logDeriv_hardyGauge_deriv_eq` | 是 |
| `ContourCancellation.lean` | 矩形边界积分 API 与解析函数闭 contour 消去 | `rectangleBoundaryIntegral`, `rectangleBoundaryIntegral_eq_zero_of_analyticOnNhd`, `RectangleBoundaryIntervalIntegrable` | 是 |
| `ContourRectangle.lean` | `ContourCancellation` 的兼容 import path，无新声明 | 无 | **否**，兼容 facade |
| `SameFormContour.lean` | Hardy 与 `Z₁` same-form correction 的解析性和边界取消 | `hardyCurvature`, `sameFormHolomorphicCorrection`, `sameFormHolomorphicCorrection_boundaryIntegral_eq_zero` | 是 |
| `PacketPolarization.lean` | finite packet sum、sharp 反射、contour coordinate 与 sesquilinear polarization | `packetSum`, `sharp`, `contourCoordinate`, `contourCoordinate_hardyReflect`, `sharp_conj`, `packetPolarization_hardyReflect_swap` | 是 |
| `PacketSameForm.lean` | packet 版 correction 消去和 Hardy/`Z₁` 边界恒等式 | `packetSameForm_integrand_decomposition`, `packetSameForm_boundaryIntegral_eq` | 是 |
| `PacketBoundaryEquality.lean` | `PacketSameForm` 的兼容 import path，无新声明 | 无 | **否**，兼容 facade |
| `PacketBoundaryIntegrability.lean` | `Z₁` packet integrand 的解析性和四边 interval integrability | `zetaOne_packetIntegrand_boundaryIntervalIntegrable`, `packetSameForm_boundaryIntegral_eq_of_nonzero` | 是 |
| `SimpleZeroLogResidue.lean` | 简单零点的 log-derivative 主系数 | `tendsto_mul_logDeriv_mul_simple_zero`, `zetaOne_packetIntegrand_simpleZero_coefficient` | 是 |
| `PacketZeroSum.lean` | weighted rectangle argument principle 和有限重数 `Z₁` zero sum | `packetZetaOne_weightedArgumentPrinciple`, `packetSameForm_zeroSum`, `exists_packetSameForm_zeroSum` | 是，当前 M02 终点 |
| `Zeta23HardyBridge.lean` | 本项目 `hardyF`/`zetaOne` 与 Zeta23 `L2`/`hardyW` 的 germ 同一 | `hardyF_eq_zeta23_L2`, `zetaOne_eq_zeta23_hardyW`, `analyticOrderAt_zetaOne_eq_zeta23_hardyW` | 是 |
| `ZetaOneAnalytic.lean` | `zetaOne` 在非实点/高矩形的解析性 | `analyticAt_zetaOne_of_im_ne_zero`, `analyticOnNhd_zetaOne_highRectangle` | 是，经 `PacketZeroSum` |

## 7. `ZeroSideStationaryGeometry/` 文件清单（M03）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `StationaryResidueBlocks.lean` | 实 stationary weight 和非实共轭 `2×2` Hermitian block | `realStationaryWeight_neg`, `conjugatePairBlock_isHermitian`, `conjugatePairQuadratic_negativeVector_neg` | 是 |
| `StationaryBlockInertia.lean` | pair block 的 codim-one good space、至多一个负维数与显式负方向 | `conjugatePair_negativeIndexLE_one`, `conjugatePair_exists_negativeDirection` | 是 |
| `StationaryResidueAnalytic.lean` | `-H(H'')²/H'` 在简单 stationary zero 的主系数 | `stationaryKernel`, `tendsto_stationaryKernel_principalCoefficient` | 是 |
| `StationarySourceBridge.lean` | Hardy gauge stationary zero/简单性与 `Z₁` 简单零点的对接 | `hardyCurvature_eq_hardyGauge_mul_deriv2_of_zetaOne_zero`, `hardyGauge_simpleStationary_iff_zetaOne_simpleZero` | 是 |
| `StationaryDictionary.lean` | 临界线上 `Z₁`, Zeta23 `hardyW`, real Hardy `Z'` 和重数字典 | `zetaOne_criticalLine_eq_zero_iff_stationary`, `zetaOne_simpleZero_criticalLine_iff_simpleStationary`, `analyticOrderNatAt_zetaOne_criticalLine_eq_wMult` | 是 |
| `StraighteningBridge.lean` | `s=1/2+iz` 坐标互换、导数、Schwarz 反射、零点与简单性传输 | `deriv_straighten`, `straighten_hardyGauge_conj`, `deriv_straighten_hardyGauge_eq_zero_iff_zetaOne_zero`, `straighten_hardyGauge_simpleStationary_iff_zetaOne_simpleZero` | 是，当前 M03 字典终点 |
| `EvaluationPullback.lean` | 有限 evaluation map 拉回、负子空间映射、负子空间上的 injectivity、negative-index 上界与满射 witness 下界 | `evaluationPullback`, `NegativeIndexWitness`, `evaluationPullback_strictlyNegativeOn_map`, `evaluationPullback_domRestrict_injective`, `evaluationPullback_negativeIndexLE`, `evaluationPullback_negativeWitness_of_surjective`, `evaluationPullback_negativeIndex_certificate` | 是，M03 G2a acceptance；G2b 仍需构造 stationary block witness |

## 8. `RightEdgeArithmeticSource/` 文件清单（M04）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `SourceAlgebra.lean` | exact/model/defect/direct residual/self-freezing 的精确代数分解 | `completedExactSource_eq_model_add_directResidual_add_freezing`, `exact_eq_finiteModel_add_directResidual_add_selfFreeze` | 是 |
| `FiniteModelFubiniLift.lean` | scalar functional error 通过 continuous linear map 与 packet integral 交换 | `continuousLinearMap_packetIntegral`, `scalarFunctionalError_packetIntegral` | 是 |
| `CurvatureCoefficient.lean` | factor-pair 和、curvature Dirichlet coefficient 与非负性 | `curvatureConvolutionCoeff_eq_squareCoeff`, `curvatureCoeff_nonneg` | 是 |
| `TranslatedPoleResidue.lean` | translated denominator/log derivative 简单零点主系数 | `translatedLogDerivative_simpleZero_coefficient`, `translatedQuotient_simpleZero_coefficient` | 是 |
| `FreezingEstimate.lean` | exact source 到 frozen source 的 norm 界 | `norm_completedExactSource_sub_frozen_le_of_bounds` | 是 |
| `StationaryPhaseGeometry.lean` | one-`χ` phase、stationary scale、导数和精确 dilation | `stationaryScale_dilation`, `deriv_oneChiPhase_eq_zero_iff_stationaryScale`, `oneChiPhase_rescale` | 是 |
| `StationaryNormalization.lean` | Stirling amplitude 与 Gaussian saddle factor 的正确归一化 | `stationaryMainPrefactor_eq_one` | 是 |
| `NonstationaryPhaseBounds.lean` | saddle 两侧的一阶导数下界 | `rightNonstationary_deriv_bound`, `leftNonstationary_deriv_bound` | 是 |
| `StationaryQuadraticControl.lean` | Hessian/三阶导数界与 Taylor 余项 | `normalizedOneChiPhase_hessian_bounds`, `thirdDeriv_normalizedOneChiPhase_abs_bound` | 是 |
| `StationaryLocalGeometry.lean` | 归一化 phase 的局部线性/二次界 | `normalizedOneChiPhase_centered_quadratic_bounds`, `oneChiPhase_gaussian_rescaling_remainder_bound` | 是 |
| `StationaryGaussianScaling.lean` | Gaussian saddle 坐标及二/三次缩放 | `stationaryGaussianCoordinate_quadratic_scale`, `stationaryGaussianCoordinate_phase_remainder` | 是 |
| `StationaryOscillationControl.lean` | exact/model oscillation 差和 amplitude freezing 的积分界 | `stationaryGaussianCoordinate_integral_oscillation_remainder`, `...amplitude_freezing_remainder` | 是 |
| `StationaryOscillatoryApproximation.lean` | exact stationary kernel 与 quadratic kernel 在 finite window 上的点态/积分误差 | `stationaryOscillatoryKernel_sub_quadratic_norm_le_on_window`, `norm_intervalIntegral_stationary_sub_quadratic_le` | 是，经 `StationaryMainTermError` |
| `QuadraticOscillatoryTail.lean` | 对 `exp(iu²/2)` 做实变量分部积分并控制 tail | `norm_intervalIntegral_quadraticOscillation_le_two_div` | 是 |
| `StationaryGaussianTail.lean` | quadratic truncation Cauchy 性与 positive Fresnel limit | `exists_positiveFresnelLimit`, `tendsto_positiveQuadraticIntegral` | 是 |
| `StationaryFresnelAbel.lean` | Abel 阻尼计算 Fresnel 常数与 `4/R` 对称窗误差 | `positiveFresnelLimit_eq_standard`, `norm_symmetricQuadraticIntegral_sub_standard_le_four_div` | 是 |
| `StationaryMainTermError.lean` | 可测/可积性，cubic replacement + Fresnel truncation 的最终有限窗界 | `norm_intervalIntegral_stationary_sub_standard_le`, `norm_intervalIntegral_stationary_sub_standard_le_sixteen_div_three_mul_inv` | 是，当前 M04 终点 |

## 9. `HLPLocalModel/` 文件清单（M05）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `ArithmeticHierarchy.lean` | Mangoldt Dirichlet 卷积幂、log coefficient、HLP `α` 层级与 support | `mangoldtConvolutionPower`, `hlpAlphaSucc`, `hlpAlphaSucc_support` | 是 |
| `ConvolutionRecurrence.lean` | HLP `α` 层的精确卷积递推 | `hlpAlphaSucc_succ_apply` | 是 |
| `AlphaDerivativeIdentity.lean` | `(k+1)α_{k+1}=log·Λ_{k+1}` 型等式 | `cast_succ_mul_hlpAlphaSucc`, `hlpAlphaSucc_eq_log_div_mangoldtPower` | 是 |
| `LambdaMeanSquareRecurrence.lean` | Mangoldt 层的 cutoff mean square 及 support-to-degree 控制 | `lambdaMeanSquare`, `pow_le_of_lambdaMeanSquare_ne_zero` | 是 |
| `WeightedChebyshev.lean` | 加权 Mangoldt kernel 与 degree gain | `weightedMangoldtKernel_le_degree_control` | 是 |
| `WeightedCauchy.lean` | 加权 Cauchy 与 HLP antidiagonal 均方界 | `weighted_sum_sq_le`, `hlpAlphaSucc_succ_sq_le_log_weighted` | 是 |
| `MeanSquareRecurrence.lean` | HLP coefficient mean square 递推 | `hlpMeanSquare`, `hlpMeanSquare_succ_le_log_antidiagonal` | 是 |
| `FactorialMajorant.lean` | lambda mean square 的 factorial 归纳步 | `lambdaMeanSquareExp_succ_le_factorial_step` | 是 |
| `FactorialInduction.lean` | 结合 Chebyshev 完成 factorial majorant | `lambdaMeanSquareExp_factorial_majorant` | 是，经 `AlphaSharpFactorialMajorant` |
| `AlphaFactorialMajorant.lean` | HLP `α` 的较粗 factorial mean-square 界 | `hlpMeanSquareExp_factorial_majorant` | 是 |
| `AlphaSharpFactorialMajorant.lean` | 利用精确 derivative identity 得到 sharp factorial gain | `hlpAlphaSharpMeanSquareExp_factorial_majorant` | 是，经 `NormalizedDirectCarrier` |
| `NaturalCutoffFactorialMajorant.lean` | 自然数 cutoff 版 factorial majorant | `hlpAlpha_nat_factorial_majorant` | 是，经 `FiniteDirectCarrier` |
| `FiniteLevelMinkowski.lean` | finite carrier vectors 的 levelwise Minkowski 界 | `sqrt_sum_sq_sum_levels_le` | 是，经 `FiniteDirectCarrier` |
| `FiniteDirectCarrier.lean` | finite coefficient carrier 的归一化平方和 | `sqrt_normalizedAlphaFiniteCarrierSquare_completed` | 是 |
| `NormalizedDirectCarrier.lean` | 单层 normalized carrier 及 factorial budget | `normalizedAlphaLevelSquare_factorial`, `normalizedAlphaLevelSquare_completed` | 是，经 `DirectCarrierAssembly` |
| `FactorialLevelSummability.lean` | `sqrt(k!)` 权及带多项式权的可求和性 | `summable_sqrtFactorialWeight`, `summable_polynomial_mul_sqrtFactorialWeight` | 是 |
| `FiniteCarrierAssembly.lean` | finite level 集合的 weighted assembly 界 | `finiteCarrierAssembly_le_tsum` | 是，经 `DirectCarrierAssembly` |
| `DirectCarrierAssembly.lean` | subset-independent direct carrier 总界 | `normalizedDirectCarrier_finiteSubset_le`, `directCarrier_polynomialWeight_finiteSubset_le` | 是，当前 carrier 终点 |
| `FiniteResolventExpansion.lean` | `1/(1-z)` 有限几何展开与 HLP tail 恒等式 | `inv_one_sub_eq_partial_add_tail`, `completedExactSource_eq_hlp_partial_add_tail` | 是 |
| `ResolventTailBound.lean` | `‖z‖<1` 下 resolvent/HLP/source tail norm 界 | `norm_resolvent_tail_le`, `norm_completedExactSource_sub_hlp_partial_le` | 是 |
| `LeadingJetResummation.lean` | leading jet 的 translated pole partial fraction/resummation | `leading_resolvent_partial_fraction`, `completed_leading_cluster` | 是 |
| `ZetaPoleLaurentBridge.lean` | zeta pole 主部 + bounded analytic remainder 接口 | `zetaPoleRemainder`, `zetaPoleP_eq_principal_add_remainder` | 是 |

## 10. M06--M10 目录文件清单

### 10.1 `GlobalModelSpectralFloor/`（M06）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `PrimitiveSchurFloor.lean` | cusp-minus-regular 下界、triangular floor、pullback/restriction 和 relative-error 稳定性 | `cusp_minus_regular_triangular_floor`, `certified_point_zero_six_floor`, `point_zero_three_floor_after_relative_error` | 是；**仅抽象 foundation** |

### 10.2 `DivisorGramArithmeticTransfer/`（M07）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `PositiveGram.lean` | finite analysis map 的 pullback Gram 二次型、kernel 和 injective 正性 | `gramQuadratic_nonnegative`, `gramQuadratic_eq_zero_iff`, `gramQuadratic_pos_of_injective` | 是 |
| `OperatorGramLift.lean` | Hilbert-valued Gram channels 与 lifted scalar form 非负性 | `sum_inner_gramChannel_eq_liftedGramForm`, `liftedGramForm_re_nonnegative` | 是 |
| `GcdGramIdentity.lean` | gcd 的 totient 展开、divisor channel 和 Hilbert Gram | `sum_totient_common_divisors`, `gcdHilbertForm_re_eq_totient_norm_sum`, `gcdHilbertForm_re_nonnegative` | 是 |
| `OperatorGcdGramLift.lean` | gcd Gram 的 operator-valued family/channel lift | `operatorGcdForm_eq_explicit`, `operatorGcdForm_eq_sum_inner_channels`, `operatorGcdForm_re_nonnegative` | 是 |

### 10.3 `FrameCompression/`（M08）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `FiniteFeatureRank.lean` | 经有限中间坐标分解的映射秩界，块 feature 和求和秩界 | `finrank_range_factor_through_coordinates_le_card`, `finrank_range_nine_features_per_block_le`, `finrank_range_add_of_two_factors_le` | 是 |
| `TranslatedPoleFeatureRank.lean` | translated pole jets 的 feature index 和秩界 | `finrank_range_translatedPoleJets_le`, `finrank_range_singleTranslatedPoleJets_le` | 是 |
| `FixedEdgeRange.lean` | finite sum 各项落在同一 fixed subspace 时的 coefficient-free range/rank/kernel-codim 界 | `range_finset_sum_le_fixed`, `finrank_range_finset_sum_le_fixed`, `codim_ker_finset_sum_le_fixed` | 是 |

### 10.4 `RetainedSpace/`（M09）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `KernelBudget.lean` | 两个/三个核的交的 codimension 预算 | `codim_inf_ker_le_range_sum`, `codim_threefold_inf_le` | 是；实际 mean maps 尚未定义 |

### 10.5 `GenericPerturbationMinMaxEndgame/`（M10）

| 文件 | 职责 | 主要声明 | facade 覆盖 |
|---|---|---|---|
| `PerturbationStability.lean` | lower bound + relative absolute perturbation 的稳定性 | `lowerBoundOn_add_of_relativeAbsBoundOn`, `negativeIndexLE_of_relative_perturbation`, `three_quarters_lowerBoundOn` | 是 |
| `PerturbedWhitenedMinMax.lean` | 四分之一扰动后的 M01 min--max | `rank_plus_hilbertSchmidt_minmax_after_quarter_perturbation` | 是 |
| `DensityOne.lean` | count gap little-o 到 `N₀/N→1` 的归一化和 dyadic paper alias | `DensityOne`, `densityOne_of_relativeCountGap_isLittleO`, `density_one_critical_line` | 是；最终 off-critical little-o 是显式未完成输入 |

## 11. 外部 `zeta-23-lean/Zeta23/` 边界

`zeta-23-lean/` 由 Lake 作为第二 source library `Zeta23` 提供参考声明。
当前 ZetaZero 主路线只依赖实际 import 到的局部根，主要包括：

- `Zeta23.Analytic.RectangleLogDeriv`：由
  `ZetaZero.Analytic.RectangleArgumentPrinciple` 包装；
- `Zeta23.XiPrime.Hardy.Basic`, `Count`, `ZeroFree`, `ZFunction`：用于
  `Zeta23HardyBridge`, `StationaryDictionary`, `ZetaOneCounting`；
- `Zeta23.Chebyshev`, `Zeta23.XiPrime.Coeff.Basic`,
  `Zeta23.XiPrime.Coeff.PowerSums`：用于 M05 系数与均方层。

以下推论均不允许：

1. 不因 `lake build ZetaZero...` 编译了若干 Zeta23 依赖，就声称
   `lake build Zeta23` 或 Zeta23 headline theorem 已验证；
2. 不把 Zeta23 的声明自动等同于论文记号；必须有像
   `zetaOne_eq_zeta23_hardyW` 这样的定向 bridge；
3. 外部 source 中的 linter/deprecation warning 与 ZetaZero 自身证明失败分开记录。

## 12. 验证状态快照

2026-08-21 已在当前工作树中执行：

```text
lake build ZetaZero.FiniteDimensionalInertiaReduction  PASS
lake build ZetaZero.HardyGaugeInvariantContourForm     PASS
lake build ZetaZero.ZeroSideStationaryGeometry         PASS
npm test -- lean-all                                   PASS (1 passed)
python3 scripts/check_lean_placeholders.py             PASS (120 files, including root facade)
npm test -- blueprint-decls                            PASS (1 passed)
python3 -m pytest                                      PASS (14 passed)
npm test -- straightening                               PASS (1 passed)
npm test -- mainline-bridge                             PASS (1 passed)
```

M03 构建期间观察到的警告来自
`zeta-23-lean/Zeta23/XiPrime/Hardy/ZFunction.lean`（`unnecessarySeqFocus` 和已弃用
`ENat.one_le_iff_ne_zero`），构建仍成功。

全 source 快照使用：

```bash
npm test -- lean-all
python3 scripts/check_lean_placeholders.py
```

Blueprint 和定向 pytest 状态使用：

```bash
npm test -- blueprint-decls
python3 -m pytest
```

原计划中的 `python3 -m pytest -q` 在当前自定义 runner 下失败，观测为
`unknown test selector(s): -q`；去掉不被支持的 quiet flag 后全量 runner 报告
`14 passed`。这是 CLI 兼容性 gap，不应误报为定理或声明失败。

即使上述 source 与定向 gate 全部 PASS，由于 Blueprint `\leanok` 与完整
`leanblueprint all` 的节点条件尚未同时封闭，也不将任何 major node 标为 green。
