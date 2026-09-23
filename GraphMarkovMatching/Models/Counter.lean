/-
Balanced counter laws and their finite-tree recursion and consistency.
-/
import GraphMarkovMatching.Process.Recursion
import GraphMarkovMatching.Process.Consistency

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

variable {V : Type}

def labRel (Rv : V → V → Prop) : V × ℕ → V × ℕ → Prop := fun s t => Rv s.1 t.1

lemma labRel_symm (Rv : V → V → Prop) (h : ∀ a b, Rv a b → Rv b a) :
    ∀ s t, labRel Rv s t → labRel Rv t s := fun _ _ hst => h _ _ hst

noncomputable def freshQ (μ : PMF V) (ν : PMF ℕ) : PMF (V × ℕ) := prodPMF μ ν

variable (μ : PMF V) (ν : PMF ℕ) (v0 : V)

noncomputable def varyK : V × ℕ → PMF ((V × ℕ) × (V × ℕ)) := fun s =>
  if 4 ≤ s.2 then PMF.pure ((v0, s.2 / 2), (v0, s.2 - s.2 / 2))
  else if s.2 = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
  else prodPMF (freshQ μ ν) (freshQ μ ν)

noncomputable def Tlaw (h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  (freshQ μ ν).bind fun s => muM (varyK μ ν v0) s h

noncomputable def Zlaw (k h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  muM (varyK μ ν v0) (v0, k) h

noncomputable def Xi (k h : ℕ) : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h) :=
  pairMix (varyK μ ν v0) (v0, k) h

noncomputable def XiBar (h : ℕ) : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h) :=
  ν.bind fun k => Xi μ ν v0 k h

lemma pairMix_varyK (v : V) (k h : ℕ) :
    pairMix (varyK μ ν v0) (v, k) h = Xi μ ν v0 k h := rfl

lemma muM_varyK_succ (v : V) (k h : ℕ) :
    muM (varyK μ ν v0) (v, k) (h + 1) = (Xi μ ν v0 k h).map (branch (v, k)) := rfl

lemma varyK_of_four_le {k : ℕ} (hk : 4 ≤ k) (v : V) :
    varyK μ ν v0 (v, k) = PMF.pure ((v0, k / 2), (v0, k - k / 2)) := by
  show (if 4 ≤ k then PMF.pure ((v0, k / 2), (v0, k - k / 2))
    else if k = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [ite_eq_left hk]

lemma varyK_three (v : V) :
    varyK μ ν v0 (v, 3) = (freshQ μ ν).map fun f => ((v0, 2), f) := by
  show (if 4 ≤ 3 then PMF.pure ((v0, 3 / 2), (v0, 3 - 3 / 2))
    else if 3 = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [ite_eq_right (by omega), ite_eq_left rfl]

lemma varyK_of_le_two {k : ℕ} (hk : k ≤ 2) (v : V) :
    varyK μ ν v0 (v, k) = prodPMF (freshQ μ ν) (freshQ μ ν) := by
  show (if 4 ≤ k then PMF.pure ((v0, k / 2), (v0, k - k / 2))
    else if k = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma Xi_of_four_le {k : ℕ} (hk : 4 ≤ k) (h : ℕ) :
    Xi μ ν v0 k h
      = prodPMF (Zlaw μ ν v0 (k / 2) h) (Zlaw μ ν v0 (k - k / 2) h) := by
  rw [Xi, pairMix, varyK_of_four_le μ ν v0 hk, PMF.pure_bind]
  rfl

lemma Xi_three (h : ℕ) :
    Xi μ ν v0 3 h = prodPMF (Zlaw μ ν v0 2 h) (Tlaw μ ν v0 h) := by
  rw [Xi, pairMix, varyK_three μ ν v0, PMF.bind_map]
  rw [show ((fun στ : (V × ℕ) × (V × ℕ) =>
        prodPMF (muM (varyK μ ν v0) στ.1 h) (muM (varyK μ ν v0) στ.2 h))
      ∘ fun f => ((v0, 2), f))
    = fun f => prodPMF (Zlaw μ ν v0 2 h) (muM (varyK μ ν v0) f h) from rfl]
  exact bind_prodPMF_const_left _ _ _

lemma Xi_of_le_two {k : ℕ} (hk : k ≤ 2) (h : ℕ) :
    Xi μ ν v0 k h = prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) := by
  rw [Xi, pairMix, varyK_of_le_two μ ν v0 hk]
  exact prodPMF_bind_prodPMF (freshQ μ ν) (freshQ μ ν)
    (fun s => muM (varyK μ ν v0) s h) (fun s => muM (varyK μ ν v0) s h)

lemma Tlaw_map_restrictLab (n : ℕ) :
    (Tlaw μ ν v0 (n + 1)).map (restrictLab n) = Tlaw μ ν v0 n :=
  mix_map_restrictLab (varyK μ ν v0) (freshQ μ ν) n

end GraphMarkovMatching
