# Lean gap closure plan: next tranche

> 日期：2026-08-21
> 目标：从文档基线进入小型、可验收的 Lean theorem chain，不把全局分析论文一次性假设化。

## 1. 选择标准

本 tranche 只选择满足以下条件的 gap：

1. mutation point/interface 已经由当前 facade 收窄；
2. 能写成 3--10 个相关声明 + 1 个 acceptance theorem；
3. 不需要把尚未证明的 zeta growth、Rouché、Jensen 或 packet asymptotic 变成假设；
4. 能在单一稳定 facade 上 build，并能用现有测试门禁复现。

## 2. 已选择的 gap

### G1 — M02 packet reflected-adjoint seam（本 tranche 已实现）

**论文位置**：`sections/01_invariant_contour.tex` 的
`eq:hardy-gauge-reflection`、`eq:packet-polarization` 及 `lem:allowed` 前后的
Hermitian contour form 叙述。
**Lean 位置**：`ZetaZero.HardyGaugeInvariantContourForm.PacketPolarization`。

接口链：

```text
hardyReflect
  -> contourCoordinate_hardyReflect
  -> sharp_conj
  -> packetPolarization_hardyReflect_swap
```

已加入的声明：

- `contourCoordinate_hardyReflect`：
  `contourCoordinate (hardyReflect s) = conj (contourCoordinate s)`；
- `sharp_conj`：`sharp B (conj z) = conj (B z)`；
- `packetPolarization_hardyReflect_swap`：交换 `v,w` 后，packet polarization
  在 Hardy reflection 下变为原式的共轭。

**Acceptance theorem**：`packetPolarization_hardyReflect_swap`。
**证据命令**：

```bash
lake env lean ZetaZero/HardyGaugeInvariantContourForm/PacketPolarization.lean
lake build ZetaZero.HardyGaugeInvariantContourForm
```

**边界**：这只关闭 packet factor 的反射/交换恒等式；没有声称已经证明
`A_T(w,v)=conj (A_T(v,w))`。边界积分的 orientation reversal、curvature/`Z₁` adjoint
和实际有限矩阵 `IsHermitian` 仍是 M02-HERMITIAN-MATRIX gap。

### G2 — M03 finite evaluation pullback（上界接口已实现；精确计数仍是下一项）

**论文位置**：`sections/02_zero_side.tex` 的 `lem:evaluation-rank` 之后，以及
`eq:zero-inertia-generic`。
**目标模块**：`ZetaZero.ZeroSideStationaryGeometry.EvaluationPullback`；该模块已由
稳定 facade `ZetaZero.ZeroSideStationaryGeometry` 导入，不形成第二套 public API。

已实现的第一层声明链：

1. 一个有限 evaluation map `E : V →ₗ[𝕜] W`（后续 node space 可取 `(ι → ℂ)`）；
2. `evaluationPullback_strictlyNegativeOn_map`：负子空间的 evaluation image
   仍为严格负子空间；
3. `evaluationPullback_domRestrict_injective`：在 `q 0 = 0` 下，严格负子空间上的
   evaluation restriction 自动 injective；
4. `NegativeIndexWitness`：记录 target 上实际存在的 `n` 维严格负子空间；
5. `evaluationPullback_negativeIndexLE`：
   `NegativeIndexLE q n` 蕴含 `NegativeIndexLE (q ∘ E) n`。
6. `evaluationPullback_negativeWitness_of_surjective`：显式 target witness 在
   `Function.Surjective E` 下拉回为 source witness；
7. acceptance theorem `evaluationPullback_negativeIndex_certificate`：同时返回上界
   与满射条件下的 witness 下界。

这层接口比直接假设 `E` 全局 injective 更弱：只在严格负子空间上得到 injectivity，
因此允许 packet evaluation 的 kernel 存在。

仍待完成的第二层声明：

8. `Function.Surjective E` 与 `LinearMap.range E = ⊤` 的 node-space bridge；
9. 从 stationary real/pair blocks 构造 target `NegativeIndexWitness`，最终给出
   `B + P` 的 paper-facing 计数接口。

**不在本项中证明**：Fourier uniqueness、Vandermonde、`ψ_L` 的 Riesz bounds、
`d_T` asymptotic、或 stationary nodes 的 existence。它们分别属于
M03-EVALUATION、M03-RIESZ、M03-DIMENSION gap，不能被 `Surjective E` 假设遮蔽。

### G3 — M03 good-height/Jensen specialization（暂缓）

现有 `Analytic/JensenZeroCount.lean` 和 `Analytic/GoodHeightCombinatorics.lean` 是
可复用抽象工具，但尚未连接到 `ζ`/`Z₁` 的中心下界、多项式增长、局部 log-derivative
因子化。该项需要较大的分析接口，暂不与 G1/G2 混合提交。

### G4 — M04 packet/Perron transfer（暂缓）

M04 的 finite-window Fresnel 与 source split 已经有强接口，但把它们接到实际 packet
source 需要同时引入 safe-line ratio、Perron deformation 和 Laurent remainder。该项
依赖 M02 的全局 specialization 以及 M05 carrier 证书，暂不提前形式化。

## 3. 执行顺序和验收门

```text
G1  packet reflected-adjoint identity       DONE
G2a finite evaluation pullback upper bound   DONE
G2b surjective/exact block count             NEXT
G3  Jensen/good-height specialization        BLOCKED ON ANALYTIC INPUTS
G4  packet/Perron transfer                   BLOCKED ON M02 + M05
```

G2a 完成后已通过：

```bash
lake build ZetaZero.ZeroSideStationaryGeometry
npm test -- lean-all
python3 scripts/check_lean_placeholders.py
npm test -- blueprint-decls
python3 -m pytest
```

若 G2b 的抽象 pullback theorem 需要把 surjectivity、Hermitian block 或 finite-dimensional
假设直接改成结论，立即停止并把缺失数学条件写回 `doc/main_tex_to_lean_system.md`，不使用
`sorry`、`admit`、项目 `axiom` 或空 theorem shell。
