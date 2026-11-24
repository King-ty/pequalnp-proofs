import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child treats graphs without triangles. The second deletes one
-- triangle edge, charging one gate for the edge and the drop in cover number.
theorem PEqualNP.Outside.R_meta_612_417
  (base : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    (∃ u v, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    ¬ (∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) → Monotone2 C →
    (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    G.edgeSet.ncard + G.vertexCoverNum.toNat ≤ C.size + 1)
  (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) → Monotone2 C →
    (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ (a b c : Fin n) (D : Circuit), G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      let H := G.deleteEdges {s(a,b)}
      Monotone2 D ∧
      (∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true)) ∧
      D.size + 1 + G.vertexCoverNum.toNat ≤ C.size + H.vertexCoverNum.toNat) :
  ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hedge hfour hcover hmin hm hf
  have go : ∀ k (H : SimpleGraph (Fin n)) (D : Circuit),
      H.edgeSet.ncard = k → (∃ u v, H.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → H.Adj a b → H.Adj b c → H.Adj c d → ¬ H.Adj d a) →
      Monotone2 D → (∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true)) →
      H.edgeSet.ncard + H.vertexCoverNum.toNat ≤ D.size + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro H D hk he h4 hmono hfun
      by_cases ht : (∃ a b c : Fin n, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a)
      · obtain ⟨a, b, c, E, hab, hbc, hca, hmono', hfun', hs⟩ :=
          peel n H D h4 ht hmono hfun
        let K := H.deleteEdges {s(a,b)}
        have heq : K.edgeSet.ncard + 1 = H.edgeSet.ncard := by
          dsimp [K]
          rw [H.edgeSet_deleteEdges]
          exact Set.ncard_sdiff_singleton_add_one (H.mem_edgeSet.mpr hab)
        have he' : K.Adj b c := by
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨hbc, ?_⟩
          simp [hca.ne, Ne.symm hab.ne, Ne.symm hbc.ne]
        have hle : K ≤ H := H.deleteEdges_le _
        have h4' : (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → K.Adj a b → K.Adj b c → K.Adj c d → ¬ K.Adj d a) := by
          intro a b c d h₁ h₂ h₃ h₄ h₅ h₆ hab hbc hcd hda
          exact h4 a b c d h₁ h₂ h₃ h₄ h₅ h₆ (hle hab) (hle hbc) (hle hcd) (hle hda)
        have small := ih K.edgeSet.ncard (by omega) K E rfl ⟨b, c, he'⟩ h4' hmono' hfun'
        change E.size + 1 + H.vertexCoverNum.toNat ≤ D.size + K.vertexCoverNum.toNat at hs
        omega
      · exact base n H D he h4 ht hmono hfun
  have bound := go _ G C rfl hedge hfour hm hf
  obtain ⟨s, hs, hv⟩ := G.vertexCoverNum_exists
  have hsc : CoverPromise.IsVertexCover G s.toFinset := by
    intro u v huv
    simpa using hv huv
  have hnum := hmin s.toFinset hsc
  have hcard : s.toFinset.card = G.vertexCoverNum.toNat := by
    rw [← hs, Set.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  omega
