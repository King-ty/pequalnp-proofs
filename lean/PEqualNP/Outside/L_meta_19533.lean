import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19533_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- The same seven-gate circuit works at every order `n`. -/
def witness (n : Nat) : Circuit :=
  ⟨[
    ⟨.or,  [1, 2 * n - 1]⟩,
    ⟨.and, [0, n]⟩,
    ⟨.not, [2 * n]⟩,
    ⟨.not, [2 * n + 1]⟩,
    ⟨.or,  [0, n]⟩,
    ⟨.or,  [2 * n + 2, 2 * n + 4]⟩,
    ⟨.and, [2 * n + 3, 2 * n + 5]⟩
  ], 2 * n + 6⟩

theorem witness_fit (n : Nat) : FanInTwo (witness n) := by
  intro g hg
  simp [witness] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega,
      by rw [h6, hl]; congr 1; omega⟩

def g0 (n u v : Nat) : Bool := decide (u = 1 ∨ v + 1 = n)
def g1 (u v : Nat) : Bool := decide (u = 0 ∧ v = 0)
def g2 (n u v : Nat) : Bool := !(g0 n u v)
def g3 (u v : Nat) : Bool := !(g1 u v)
def g4 (u v : Nat) : Bool := decide (u = 0 ∨ v = 0)
def g5 (n u v : Nat) : Bool := g2 n u v || g4 u v
def g6 (n u v : Nat) : Bool := g3 u v && g5 n u v

def value (n u v w : Nat) : Bool :=
  if w < n then decide (u = w)
  else if w < 2 * n then decide (v + n = w)
  else match w - 2 * n with
    | 0 => g0 n u v
    | 1 => g1 u v
    | 2 => g2 n u v
    | 3 => g3 u v
    | 4 => g4 u v
    | 5 => g5 n u v
    | 6 => g6 n u v
    | _ => false

def gate (n k : Nat) : Gate :=
  match k with
  | 0 => ⟨.or,  [1, 2 * n - 1]⟩
  | 1 => ⟨.and, [0, n]⟩
  | 2 => ⟨.not, [2 * n]⟩
  | 3 => ⟨.not, [2 * n + 1]⟩
  | 4 => ⟨.or,  [0, n]⟩
  | 5 => ⟨.or,  [2 * n + 2, 2 * n + 4]⟩
  | _ => ⟨.and, [2 * n + 3, 2 * n + 5]⟩

theorem value_x (n u v w : Nat) (h : w < n) :
    value n u v w = decide (u = w) := by simp [value, h]

theorem value_y (n u v w : Nat) (h1 : n ≤ w) (h2 : w < 2 * n) :
    value n u v w = decide (v + n = w) := by
  simp [value, h2, show ¬ w < n by omega]

theorem value_g (n u v k : Nat) : value n u v (2 * n + k) =
    match k with
    | 0 => g0 n u v
    | 1 => g1 u v
    | 2 => g2 n u v
    | 3 => g3 u v
    | 4 => g4 u v
    | 5 => g5 n u v
    | 6 => g6 n u v
    | _ => false := by
  have h1 : ¬ 2 * n + k < n := by omega
  have h2 : ¬ 2 * n + k < 2 * n := by omega
  simp [value, h1, h2]

theorem gate_ok (n u v k : Nat) (hn : 3 ≤ n) (hk : k < 7) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (value n u v)) =
        value n u v (2 * n + k) := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [gate, List.mem_cons, List.not_mem_nil, or_false, List.map,
      GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
      List.headD_cons, id, Bool.or_false, Bool.and_true] <;>
    constructor
  all_goals try { intro i hi; rcases hi with rfl | rfl <;> omega }
  · rw [value_x n u v 1 (by omega), value_y n u v (2*n-1) (by omega) (by omega), value_g]
    apply Bool.eq_iff_iff.2
    simp [g0]
    omega
  · rw [value_x n u v 0 (by omega), value_y n u v n (by omega) (by omega), value_g]
    simp [g1]
  · rw [show 2 * n = 2 * n + 0 by omega, value_g]
    simp only [Nat.add_zero]
    rw [value_g]
    simp [g2]
  · rw [value_g, value_g]
    simp [g3]
  · rw [value_x n u v 0 (by omega), value_y n u v n (by omega) (by omega), value_g]
    simp [g4]
  · rw [value_g, value_g, value_g]
    simp [g5]
  · rw [value_g, value_g, value_g]
    simp [g6]

theorem eval_witness (n : Nat) (hn : 3 ≤ n) (u v : Fin n) :
    (witness n).eval (oneEach u v) = g6 n u.val v.val := by
  have hl : (oneEach u v).length = 2 * n := by
    simp [oneEach]
    omega
  have hx : ∀ i < (oneEach u v).length,
      (oneEach u v).getD i false = value n u.val v.val i := by
    intro i hi
    rw [hl] at hi
    apply Bool.eq_iff_iff.2
    simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
      List.length_ofFn, List.getElem?_ofFn, value]
    split_ifs <;> simp [Fin.ext_iff] <;> omega
  change
    ([⟨.or, [1, 2*n-1]⟩, ⟨.and, [0,n]⟩, ⟨.not,[2*n]⟩,
      ⟨.not,[2*n+1]⟩, ⟨.or,[0,n]⟩, ⟨.or,[2*n+2,2*n+4]⟩,
      ⟨.and,[2*n+3,2*n+5]⟩].foldl stp (oneEach u v)).getD (2*n+6) false = _
  rw [spec (value n u.val v.val) _ _ hx (fun k hk => by
    simp only [List.length_cons, List.length_nil] at hk
    rw [hl]
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only
      [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      exact gate_ok n u.val v.val _ hn (by omega))
    _ (by simp [hl])]
  simpa using value_g n u.val v.val 6

/-- The graph described in the task: row zero misses column zero; row one only
contains column zero; every later row misses just the last column. -/
def target (n : Nat) (u v : Fin n) : Bool :=
  decide ((u.val = 0 ∧ v.val ≠ 0) ∨
          (u.val = 1 ∧ v.val = 0) ∨
          (2 ≤ u.val ∧ v.val + 1 ≠ n))

theorem g6_target (n u v : Nat) (hn : 3 ≤ n) (_hu : u < n) (hv : v < n) :
    g6 n u v = decide ((u = 0 ∧ v ≠ 0) ∨
      (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ v + 1 ≠ n)) := by
  apply Bool.eq_iff_iff.2
  simp [g6, g5, g4, g3, g2, g1, g0]
  omega

end PEqualNP.Outside.L_meta_19533_aux

open PEqualNP.Outside.L_meta_19533_aux
  PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19533 : ∀ n : Nat, 3 ≤ n →
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
      Represents (fun (u v : Fin n) => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨
        (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) C := by
  intro n hn
  refine ⟨witness n, witness_fit n, by simp [Circuit.size, witness], ?_⟩
  intro u v
  have hu : u.val < n := u.isLt
  have hv : v.val < n := v.isLt
  rw [eval_witness n hn u v, g6_target n u.val v.val hn hu hv]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  omega

