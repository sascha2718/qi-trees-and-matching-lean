/- Asymmetric bridges used by the two-law Hall screen rows. -/
import GraphMarkovMatching.Rows.ECore
import GraphMarkovMatching.Archive.VaryingTwoLawLedger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (νL νR : PMF ℕ) (v0 : V)

lemma crossInterpScreen_zsucc_none (SR : Finset ℕ) (h : ℕ) (c' : Tgt)
    (z : Finset Tgt) :
    crossInterpScreen α Rv μ νL νR v0 h ⟨c', zsucc SR z, none⟩
      = screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
          (((zsucc SR z).toList).map (interpT μ νR v0 h))
          (fun _ => (1 : ℝ≥0∞)) := rfl

lemma crossInterpScreen_zsucc_some (SR : Finset ℕ) (h : ℕ)
    (c' w' : Tgt) (z : Finset Tgt) :
    crossInterpScreen α Rv μ νL νR v0 h ⟨c', zsucc SR z, some w'⟩
      = screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
          (((zsucc SR z).toList).map (interpT μ νR v0 h))
          (WresD α (interpT μ νR v0 h w')
            (fullSim (labRel Rv) h)) := rfl

lemma mem_crossScreenSucc_mk {SL SR : Finset ℕ} {c t' : Tgt}
    {z : Finset Tgt} {u u' : Option Tgt}
    (ht : t' ∈ tgtSucc SL c) (hu : u' ∈ normSucc SR u) :
    (⟨t', zsucc SR z, u'⟩ : GScreen) ∈ crossScreenSucc SL SR ⟨c, z, u⟩ :=
  Finset.mem_image.mpr
    ⟨(t', u'), Finset.mem_product.mpr ⟨ht, hu⟩, rfl⟩

lemma crossInterp_le_succ_sum (h : ℕ) {SL SR : Finset ℕ}
    {sc sc' : GScreen} (hmem : sc' ∈ crossScreenSucc SL SR sc) :
    crossInterpScreen α Rv μ νL νR v0 h sc'
      ≤ ∑ sc'' ∈ crossScreenSucc SL SR sc,
          crossInterpScreen α Rv μ νL νR v0 h sc'' :=
  Finset.single_le_sum (fun _ _ => zero_le) hmem

end GraphMarkovMatching
