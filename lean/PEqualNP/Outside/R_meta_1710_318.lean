import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Peel every nonisolated vertex below the threshold. The edges paid for in
-- this phase are bounded by the threshold times the original support size.
-- All deleted inputs can be set to false in a single circuit restriction.
theorem PEqualNP.Outside.R_meta_1710_318
  (restrictZero : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (S : Set (Fin n)) (C : Circuit), (∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S) →
    Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = NestedCover.graphFun H ∅ ∧ D.size ≤ C.size + 1)
  (dense : ∃ d c : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, H.degree v = 0 ∨ d + 4 ≤ H.degree v) →
    (∀ v (w : H.Walk v v), w.IsCycle → 5 ≤ w.length) → ∀ D : Circuit,
    Monotone2 D → circuitFun n D = NestedCover.graphFun H ∅ → H.edgeFinset.card ≤ c * (D.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  have support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
    Fintype.card G.support ≤ 2 * (C.size + 1) := by
    intro n G _ C hm hf
    classical
    let wires := C.output :: C.gates.flatMap Gate.inputs
    have occurs (p : G.support) : p.val.val ∈ wires := by
      by_contra hp
      have hp' : C.output ≠ p.val.val ∧ p.val.val ∉ C.gates.flatMap Gate.inputs := by
        simpa [wires, eq_comm] using hp
      obtain ⟨v,hv⟩ := p.property
      let x : Fin n → Bool := fun i => decide (i = p.val ∨ i = v)
      let y : Fin n → Bool := fun i => decide (i = v)
      have one : NestedCover.graphFun G ∅ x = true := by
        delta NestedCover.graphFun
        simpa using
          (show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from ⟨p, v, hv, by simp [x], by simp [x]⟩)
      have zero : NestedCover.graphFun G ∅ y = false := by
        delta NestedCover.graphFun
        simp [y]
      let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have propagate (gs : List Gate) (unused : p.val.val ∉ gs.flatMap Gate.inputs)
          (a b : List Bool) (len : a.length = b.length)
          (off : ∀ i, i ≠ p.val.val → a.getD i false = b.getD i false) :
          ∀ i, i ≠ p.val.val → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
        induction gs generalizing a b with
        | nil => exact off
        | cons g gs ih =>
          simp only [List.flatMap_cons,List.mem_append,not_or] at unused
          apply ih unused.2
          · simp [step,len]
          · intro i hi
            have same : (g.inputs.map fun j => a.getD j false) = g.inputs.map fun j => b.getD j false := by
              apply List.map_congr_left
              intro j hj
              exact off j (fun h => unused.1 (h ▸ hj))
            dsimp only [step]
            rw [same]
            by_cases lt : i < a.length
            · rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ (by omega)]
              exact off i hi
            · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
      have eq : circuitFun n C x = circuitFun n C y := by
        apply propagate C.gates hp'.2 _ _ (by simp) _ C.output hp'.1
        intro i hi
        by_cases lt : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using lt),List.getD_eq_getElem _ _ (by simpa using lt)]
          have ne : (⟨i,lt⟩ : Fin n) ≠ p.val := fun h => hi (congrArg Fin.val h)
          simp [x,y,ne]
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
      rw [hf,one,zero] at eq
      contradiction
    let f : G.support → ↥wires.toFinset := fun p => ⟨p.val.val, List.mem_toFinset.mpr (occurs p)⟩
    have fi : Function.Injective f := by
      intro a b h
      exact Subtype.ext (Fin.ext (congrArg Subtype.val h))
    have hcard := Fintype.card_le_of_injective f fi
    have sumBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have ha := h g (by simp)
        have hb := ih (fun q hq => h q (by simp [hq]))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        omega
    have hb := sumBound C.gates (fun g hg => (hm g hg).2)
    have count := wires.toFinset_card_le
    simp only [Fintype.card_coe] at hcard
    simp only [wires,List.length_cons] at count
    dsimp only [wires] at hcard
    change Fintype.card G.support ≤ 2 * (C.gates.length + 1)
    omega
  obtain ⟨d, c, core⟩ := dense
  let k := d + 4
  refine ⟨2 * c + 2 * k, ?_⟩
  intro n G _ _ girth C cm computes
  have cg : circuitFun n C = NestedCover.graphFun G ∅ := by
    funext x
    rw [computes]
    delta NestedCover.graphFun
    simp
  have peel : ∀ m (K : SimpleGraph (Fin n)) [DecidableRel K.Adj],
      Fintype.card K.support = m →
      ∃ (S : Set (Fin n)) (H : SimpleGraph (Fin n)) (_ : DecidableRel H.Adj),
        (∀ u v, H.Adj u v ↔ K.Adj u v ∧ u ∈ S ∧ v ∈ S) ∧
        (∀ v, H.degree v = 0 ∨ k ≤ H.degree v) ∧
        K.edgeFinset.card ≤ H.edgeFinset.card + k * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro K _ hm
      by_cases ok : ∀ v, K.degree v = 0 ∨ k ≤ K.degree v
      · exact ⟨Set.univ, K, inferInstance, by simp, ok, by omega⟩
      push Not at ok
      obtain ⟨v, hn, hd⟩ := ok
      have hv := (K.degree_pos_iff_mem_support v).mp (Nat.pos_of_ne_zero hn)
      let J := K.deleteIncidenceSet v
      have ha := K.card_support_deleteIncidenceSet hv
      have hmpos : 0 < Fintype.card K.support := Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
      have hm' : Fintype.card J.support + 1 ≤ m := by
        change Fintype.card (K.deleteIncidenceSet v).support + 1 ≤ m
        omega
      obtain ⟨S, H, inst, eqH, degH, edges⟩ := ih (Fintype.card J.support) (by omega) J rfl
      refine ⟨S ∩ {v}ᶜ, H, inst, ?_, degH, ?_⟩
      · intro u w
        rw [eqH, SimpleGraph.deleteIncidenceSet_adj]
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
        tauto
      · have step : J.edgeFinset.card = K.edgeFinset.card - K.degree v :=
          K.card_edgeFinset_deleteIncidenceSet v
        have mul := Nat.mul_le_mul_left k hm'
        rw [Nat.mul_add_one] at mul
        omega
  obtain ⟨S, H, inst, induced, degH, edges⟩ := peel _ G rfl
  have sub : H ≤ G := fun u v huv => ((induced u v).mp huv).1
  have hg : ∀ v (w : H.Walk v v), w.IsCycle → 5 ≤ w.length := by
    intro v w hw
    have hh : (w.mapLe sub).IsCycle := (SimpleGraph.Walk.isCycle_mapLe sub).mpr hw
    simpa using girth v (w.mapLe sub) hh
  obtain ⟨D, dm, df, ds⟩ := restrictZero n G H S C induced cm cg
  have hc := core n H degH hg D dm df
  have hs := support n G C cm cg
  have hcore := Nat.mul_le_mul_left c (show D.size + 1 ≤ 2 * (C.size + 1) by omega)
  have hsupp := Nat.mul_le_mul_left k hs
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card + k * Fintype.card G.support := edges
    _ ≤ c * (2 * (C.size + 1)) + k * (2 * (C.size + 1)) :=
      Nat.add_le_add (hc.trans hcore) hsupp
    _ = _ := by ring
