import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Filter Set
open scoped Topology

/- Frames: Full Parameters, @FunctionName, and First Break.
   Fill the six small holes first. Then pass those facts explicitly to
   Mathlib's L'Hopital theorem in the final exercise. -/

theorem chain_full
    (Alpha : Type) (R : Alpha -> Alpha -> Prop)
    (u v w : Alpha)
    (huv : R u v) (hvw : R v w)
    (htrans : ∀ {a b c : Alpha}, R a b -> R b c -> R a c) :
    R u w := by
  exact htrans huv hvw

#eval List.map Nat.succ [1, 2, 3]
#eval @List.map Nat Nat Nat.succ [1, 2, 3]

theorem sin_derivative_near_zero :
    ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt Real.sin (Real.cos x) x := by
  filter_upwards with x
  exact sorry

theorem id_derivative_near_zero :
    ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun y : ℝ => y) 1 x := by
  filter_upwards with x
  exact sorry

theorem id_derivative_nonzero_near_zero :
    ∀ᶠ _x in 𝓝 (0 : ℝ), (1 : ℝ) ≠ 0 := by
  sorry

theorem sin_tends_to_zero :
    Tendsto Real.sin (𝓝 (0 : ℝ)) (𝓝 0) := by
  sorry

theorem id_tends_to_zero :
    Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 0) := by
  sorry

theorem derivative_ratio_tends_to_one :
    Tendsto (fun x : ℝ => Real.cos x / 1) (𝓝 (0 : ℝ)) (𝓝 1) := by
  sorry

theorem tendsto_sin_div_id :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  exact @HasDerivAt.lhopital_zero_nhds
    0 (𝓝 1) Real.sin Real.cos (fun x : ℝ => x) (fun _x : ℝ => 1)
    sin_derivative_near_zero
    id_derivative_near_zero
    id_derivative_nonzero_near_zero
    sin_tends_to_zero
    id_tends_to_zero
    derivative_ratio_tends_to_one
