import PEqualNP.Defs
-- King-ty compares the ordinary inputs with a free complement of input zero.
-- The full graph forest and projection proofs are adapted from PressF10 and loris-olsem, PR 4332.
-- The signed binary-gate certificate is adapted from Great-Leader-of-ISLAND, PR 5922.
-- The signed-word translation and grouping of finite decisions are from King-ty's L-meta-3178 development.
namespace PEqualNP.Outside.L_meta_3415
namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

 

inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

theorem simulate_all_wires (empty : ρ) {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Ordinary raw n ws) :
    ∃ ys, Free (raw.map (norm empty)) n ys ∧
          ∀ a ∈ ws, norm empty a ∈ ys := by
  induction run with
  | start =>
    exact ⟨_, Free.start, fun a ha => List.mem_map_of_mem ha⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hy,old⟩ := ih
    refine ⟨ys,hy,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_unary]
      exact old a ha
    · exact old w was
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hy,old⟩ := ih
    let kk := normalizedKind join (a empty) (b empty)
    have fresh := Free.binary hy kk (old a ha) (old b hb)
    refine ⟨_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_binary]
      simp [kk]
    · exact List.mem_cons_of_mem _ (old w was)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

def absentBit : ρ → Bool := fun _ => false
def ins {α : Type} (a : α) (U : α → Prop) : α → Prop := fun v => v = a ∨ U v

 

inductive Live (goal : ρ → Bool) : Nat → ((ρ → Bool) → Prop) → Prop
  | stop : Live goal 0 (fun v => v=goal)
  | step {k U a b} (kind : Kind) (ab : a≠b)
      (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Live goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Live goal (k+1) (ins a (ins b U))

private theorem same_result (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) (a i)) = a ∨
    (fun i => applyKind kind (a i) (a i)) = absentBit := by
  cases kind with
  | conj => left; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => right; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem zero_left (kind : Kind) (b : ρ → Bool) :
    (fun i => applyKind kind false (b i)) = b ∨
    (fun i => applyKind kind false (b i)) = absentBit := by
  cases kind with
  | conj => right; rfl
  | disj => left; funext i; cases b i <;> rfl
  | leftOnly => right; rfl
  | rightOnly => left; funext i; cases b i <;> rfl

private theorem zero_right (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) false) = a ∨
    (fun i => applyKind kind (a i) false) = absentBit := by
  cases kind with
  | conj => right; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => left; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem free_keeps_raw {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Free raw n ws) {v} (h : v∈raw) : v∈ws := by
  induction run with
  | start => exact h
  | binary _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem rewind {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Live goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Live goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Live goal (k+1) (ins a (ins b U)) :=
          Live.step kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

theorem Live.separates {goal : ρ → Bool} {S k} (h : Live goal k S)
    (pos neg : ρ) (different : goal pos≠goal neg) :
    ∃ w, S w ∧ w pos≠w neg := by
  induction h with
  | stop => exact ⟨goal,rfl,different⟩
  | @step n U a b kind hab ha hb hf tail ih =>
    obtain ⟨w,hw,diff⟩ := ih
    rcases hw with eq | inU
    · subst w
      by_cases ea : a pos=a neg
      · refine ⟨b,Or.inr (Or.inl rfl),?_⟩
        intro eb
        apply diff
        change applyKind kind (a pos) (b pos) = applyKind kind (a neg) (b neg)
        rw [ea,eb]
      · exact ⟨a,Or.inl rfl,ea⟩
    · exact ⟨w,Or.inr (Or.inr inU),diff⟩

private def eraseOnce {α : Type} [DecidableEq α] (v : α) : List α → List α
  | [] => []
  | x::xs => if x=v then xs else x::eraseOnce v xs

private theorem erase_len {α : Type} [DecidableEq α] (v : α) (xs : List α) (h : v∈xs) :
    (eraseOnce v xs).length+1=xs.length := by
  induction xs with
  | nil => simp at h
  | cons a l ih =>
    by_cases e : a=v
    · simp [eraseOnce,e]
    · have hit : v∈l := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      have hlen := ih hit
      simp [eraseOnce,e]
      omega

private theorem erase_preserves {α : Type} [DecidableEq α] {v w : α} (hw : w≠v)
    (xs : List α) (hin : w∈xs) : w∈eraseOnce v xs := by
  induction xs with
  | nil => simp at hin
  | cons a l ih =>
    by_cases e : a=v
    · subst a
      simpa [eraseOnce] using (List.mem_cons.mp hin).resolve_left hw
    · simp only [eraseOnce,if_neg e,List.mem_cons]
      rcases List.mem_cons.mp hin with eq | old
      · exact Or.inl eq
      · exact Or.inr (ih old)

theorem Live.width_cover {goal : ρ → Bool} {S k} (h : Live goal k S) :
    ∃ xs : List (ρ→Bool), xs.length≤k+1 ∧ ∀ w, S w → w∈xs := by
  classical
  induction h with
  | stop =>
    refine ⟨[goal],by simp,?_⟩
    intro w eq
    change w=goal at eq
    subst w
    simp
  | @step n U a b kind hab ha hb fresh tail ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    obtain ⟨xs,len,sub⟩ := ih
    have inside : z∈xs := sub z (Or.inl rfl)
    have reduced := erase_len z xs inside
    refine ⟨a::b::eraseOnce z xs,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      rcases hw with eq | eq | hu
      · simp [eq]
      · simp [eq]
      · have ne : w≠z := by
          intro eq
          apply fresh
          exact Or.inr (Or.inr ((congrArg U eq).mp hu))
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (erase_preserves ne xs (sub w (Or.inr hu))))

end CoThetaFreeCore

namespace CoThetaFreeCore

def primary {ι : Type} (j : ι) (x : ι → Bool) := x j

theorem necessary_primary {ι : Type} {goal : (ι → Bool) → Bool} {S k}
    (run : Live goal k S) (j : ι)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i)
    (sens : ∃ p n, goal p≠goal n ∧ ∀ i, i≠j → p i=n i) :
    S (primary j) := by
  obtain ⟨p,n,diff,rest⟩ := sens
  obtain ⟨wire,hw,dis⟩ := run.separates p n diff
  rcases inputs wire hw with c | ⟨i,c⟩
  · subst wire
    exact (dis rfl).elim
  · subst wire
    by_cases eq : i=j
    · exact eq ▸ hw
    · exact (dis (rest i eq)).elim

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def neigh (i : Fin 7) : Fin 7 := match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | _ => 1

def single (j : Fin 7) (i : Fin 7) : Bool := i == neigh j
def edgeRow (j : Fin 7) (i : Fin 7) : Bool := single j i || i==j

theorem theta_rows : ∀ j : Fin 7, theta (single j) = false ∧ theta (edgeRow j) = true := by decide

theorem theta_needs_every_input {S k} (run : Live theta k S)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i) : ∀ j, S (primary j) := by
  intro j
  apply necessary_primary run j inputs
  refine ⟨single j,edgeRow j,?_,?_⟩
  · rw [(theta_rows j).1,(theta_rows j).2]
    decide
  · intro i h
    simp [edgeRow,h]

end CoThetaFreeCore

namespace CoThetaFreeCore

structure TraceGate (ρ : Type) where
  kind : Kind
  left : ρ → Bool
  right : ρ → Bool

def TraceGate.value {ρ} (g : TraceGate ρ) : ρ → Bool :=
  fun r => applyKind g.kind (g.left r) (g.right r)

def registered {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → Prop
  | [] => True
  | g::gs => g.left∈raw ∧ g.right∈raw ∧ registered (g.value::raw) gs

def traceWires {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → List (ρ→Bool)
  | [] => raw
  | g::gs => traceWires (g.value::raw) gs

def restrict {ρ σ} (lift : σ→ρ) (wire : ρ→Bool) : σ→Bool := fun i => wire (lift i)

def disappears {ρ σ} (lift : σ→ρ) (g : TraceGate ρ) : Prop :=
  restrict lift g.left=absentBit ∨ restrict lift g.right=absentBit

noncomputable def remaining {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 0 else 1) + remaining lift gs

noncomputable def saved {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 1 else 0) + saved lift gs

theorem accounted {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    remaining lift gs + saved lift gs = gs.length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [remaining,saved,h] <;> omega

private theorem trace_step {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    {init pool : List (σ→Bool)} {n} (live : Free init n pool)
    (ha : restrict lift g.left∈pool) (hb : restrict lift g.right∈pool)
    (hz : absentBit∈pool) :
    ∃ k ys, (disappears lift g → k=0) ∧ (¬disappears lift g → k=1) ∧
      Free init (n+k) ys ∧ (∀ a∈pool,a∈ys) ∧ restrict lift g.value∈ys := by
  classical
  by_cases drop : disappears lift g
  · refine ⟨0,pool,fun _ => rfl,fun n => (n drop).elim,live,fun _ h => h,?_⟩
    change (fun r => applyKind g.kind (restrict lift g.left r) (restrict lift g.right r))∈pool
    rcases drop with lo|lo
    · rw [lo]
      rcases zero_left g.kind (restrict lift g.right) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr hb
      · exact (congrArg (fun v => v∈pool) e).mpr hz
    · rw [lo]
      rcases zero_right g.kind (restrict lift g.left) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr ha
      · exact (congrArg (fun v => v∈pool) e).mpr hz
  · exact ⟨1,_,fun h => (drop h).elim,fun _ => rfl,Free.binary live g.kind ha hb,
      fun _ h => List.mem_cons_of_mem _ h,List.mem_cons_self⟩

theorem restrict_trace {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ))
    {start : List (ρ→Bool)} {init pool : List (σ→Bool)} {n}
    (good : registered start gs) (pre : Free init n pool) (hz : absentBit∈pool)
    (known : ∀ w∈start,restrict lift w∈pool) :
    ∃ ys, Free init (n+remaining lift gs) ys ∧ ∀ w∈traceWires start gs,restrict lift w∈ys := by
  classical
  induction gs generalizing start pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons g gs ih =>
    rcases good with ⟨left,right,rest⟩
    obtain ⟨k,mid,zeroCost,oneCost,step,old,output⟩ :=
      trace_step lift g pre (known _ left) (known _ right) hz
    have fresh (w) (h : w∈g.value::start) : restrict lift w∈mid := by
      rcases List.mem_cons.mp h with e|h
      · exact (congrArg (fun v => restrict lift v∈mid) e).mpr output
      · exact old _ (known _ h)
    obtain ⟨ys,tail,available⟩ := ih rest step (old _ hz) fresh
    refine ⟨ys,?_,available⟩
    by_cases d : disappears lift g
    · have eq := zeroCost d
      simpa [remaining,d,eq] using tail
    · have eq := oneCost d
      simpa [remaining,d,eq,Nat.add_assoc] using tail

end CoThetaFreeCore

namespace CoThetaFreeCore

theorem trace_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    traceWires raw (a++b)=traceWires (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => rfl
  | cons x xs ih => exact ih (x.value::raw)

theorem registered_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    registered raw (a++b) ↔ registered raw a ∧ registered (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => simp [registered,traceWires]
  | cons x xs ih =>
    simp only [List.cons_append,registered,traceWires,ih]
    simp [and_assoc]

theorem trace_of_free {ρ} {raw ws : List (ρ→Bool)} {n} (p : Free raw n ws) :
    ∃ gs : List (TraceGate ρ), gs.length=n ∧ registered raw gs ∧ traceWires raw gs=ws := by
  induction p with
  | start => exact ⟨[],rfl,True.intro,rfl⟩
  | @binary n ws a b pre kind ha hb ih =>
    obtain ⟨s,len,reg,eq⟩ := ih
    let g : TraceGate ρ := ⟨kind,a,b⟩
    refine ⟨s++[g],by simp [len],(registered_append _ _ _).2 ⟨reg,?_⟩,?_⟩
    · simpa [eq,registered,g] using And.intro ha hb
    · rw [trace_append,eq]
      rfl

def reads {ρ} (g : TraceGate ρ) (wire : ρ→Bool) : Prop := g.left=wire ∨ g.right=wire

theorem reading_zero_disappears {ρ σ} (lift : σ→ρ) {g : TraceGate ρ} {wire}
    (drop : restrict lift wire=absentBit) (h : reads g wire) : disappears lift g := by
  rcases h with e|e
  · exact Or.inl ((congrArg (restrict lift) e).trans drop)
  · exact Or.inr ((congrArg (restrict lift) e).trans drop)

theorem two_zero_propagate {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    (l : restrict lift g.left=absentBit) (r : restrict lift g.right=absentBit) :
    restrict lift g.value=absentBit := by
  funext i
  change applyKind g.kind (restrict lift g.left i) (restrict lift g.right i) = false
  rw [l,r]
  cases g.kind <;> rfl

end CoThetaFreeCore
namespace CoThetaFreeCore

def agreeOutside {ρ : Type} (E : (ρ → Bool) → Prop) (r s : ρ)
    (ws : List (ρ → Bool)) : Prop := ∀ w∈ws, ¬ E w → w r = w s

theorem trace_barrier {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    (gs : List (TraceGate ρ)) {raw} (well : registered raw gs)
    (sources : agreeOutside E r s raw)
    (blocked : ∀ g∈gs, (E g.left ∨ E g.right) → g.value r=g.value s) :
    agreeOutside E r s (traceWires raw gs) := by
  classical
  induction gs generalizing raw with
  | nil => exact sources
  | cons g gs ih =>
    rcases well with ⟨hl,hr,rest⟩
    have same : g.value r=g.value s := by
      by_cases h : E g.left ∨ E g.right
      · exact blocked g (by simp) h
      · have le := sources g.left hl (fun x => h (Or.inl x))
        have re := sources g.right hr (fun x => h (Or.inr x))
        simp only [TraceGate.value,le,re]
    apply ih rest _ (fun t ht => blocked t (List.mem_cons_of_mem _ ht))
    intro w hw n
    rcases List.mem_cons.mp hw with e|h
    · exact e ▸ same
    · exact sources w h n

theorem reader_witness {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (well : registered raw gs)
    (sources : agreeOutside E r s raw) (hOut : out∈traceWires raw gs)
    (clear : ¬ E out) (diff : out r ≠ out s) :
    ∃ g∈gs, (E g.left ∨ E g.right) ∧ g.value r≠g.value s := by
  classical
  apply Classical.byContradiction
  intro bad
  apply diff
  apply trace_barrier E r s gs well sources _ out hOut clear
  intro g hg he
  apply Classical.byContradiction
  intro ne
  exact bad ⟨g,hg,he,ne⟩

theorem second_reader {ρ : Type} (x : ρ→Bool) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (gate : TraceGate ρ)
    (well : registered raw gs) (source : agreeOutside (·=x) r s raw)
    (hOut : out∈traceWires raw gs) (distinct : out≠x) (diff : out r ≠ out s)
    (masked : gate.value r=gate.value s) :
    ∃ g∈gs, reads g x ∧ g≠gate := by
  obtain ⟨g,hg,reader,ne⟩ := reader_witness (·=x) r s well source hOut distinct diff
  exact ⟨g,hg,reader,fun e => ne (e ▸ masked)⟩

end CoThetaFreeCore
namespace CoThetaFreeCore

def sufficient {ρ : Type} (raw : List (ρ→Bool)) (out : ρ→Bool)
    (gs : List (TraceGate ρ)) : Prop := registered raw gs ∧ out∈traceWires raw gs

def freshTrace {ρ : Type} (raw : List (ρ→Bool)) : List (TraceGate ρ)→Prop
  | [] => True
  | g::gs => g.value∉raw ∧ freshTrace (g.value::raw) gs

theorem trace_subset {ρ : Type} (gs : List (TraceGate ρ)) {as bs}
    (sub : ∀ w∈as,w∈bs) :
    (registered as gs → registered bs gs) ∧
      ∀ w∈traceWires as gs,w∈traceWires bs gs := by
  induction gs generalizing as bs with
  | nil => exact ⟨fun _ => True.intro,sub⟩
  | cons g tail ih =>
    have next : ∀ w∈g.value::as,w∈g.value::bs := by
      intro w hw
      rcases List.mem_cons.mp hw with e|h
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (sub _ h)
    have h := ih next
    exact ⟨fun ok => ⟨sub _ ok.1,sub _ ok.2.1,h.1 ok.2.2⟩,h.2⟩

theorem simplify_trace {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    (gs : List (TraceGate ρ)) (solves : sufficient raw out gs) :
    ∃ ts : List (TraceGate ρ), sufficient raw out ts ∧ freshTrace raw ts ∧
      (ts.length≤gs.length ∧ (¬freshTrace raw gs → ts.length<gs.length)) := by
  classical
  induction gs generalizing raw with
  | nil => exact ⟨[],solves,True.intro,Nat.le_refl _,fun bad => (bad True.intro).elim⟩
  | cons g gs ih =>
    obtain ⟨reg,output⟩ := solves
    rcases reg with ⟨left,right,rest⟩
    by_cases seen : g.value∈raw
    · have cover : ∀ w∈g.value::raw,w∈raw := by
        intro w h
        rcases List.mem_cons.mp h with e|h
        · exact e ▸ seen
        · exact h
      have reduce := trace_subset gs cover
      obtain ⟨ts,ok,fresh,le,_⟩ := ih ⟨reduce.1 rest,reduce.2 out output⟩
      refine ⟨ts,ok,fresh,?_,?_⟩ <;> simp only [List.length_cons] <;> omega
    · obtain ⟨ts,ok,fresh,le,lt⟩ := ih ⟨rest,output⟩
      refine ⟨g::ts,⟨⟨left,right,ok.1⟩,ok.2⟩,⟨seen,fresh⟩,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro bad
        have h := lt (fun f => bad (And.intro seen f))
        simp only [List.length_cons]
        omega

theorem trace_minimal_fresh {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    {gs : List (TraceGate ρ)} (solves : sufficient raw out gs)
    (minimal : ∀ ts, sufficient raw out ts → gs.length≤ts.length) : freshTrace raw gs := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨ts,h,_,_,lt⟩ := simplify_trace gs solves
  have small := lt bad
  have big := minimal ts h
  omega

theorem fresh_outputs {ρ : Type} {raw : List (ρ→Bool)} {gs : List (TraceGate ρ)}
    (fresh : freshTrace raw gs) (g : TraceGate ρ) (hg : g∈gs) : g.value∉raw := by
  induction gs generalizing raw with
  | nil => simp at hg
  | cons t ts ih =>
    rcases fresh with ⟨ft,fs⟩
    rcases List.mem_cons.mp hg with e|h
    · exact e ▸ ft
    · exact fun hRaw => ih fs h (List.mem_cons_of_mem _ hRaw)

end CoThetaFreeCore
namespace CoThetaFreeCore

def pairCode (op : Kind) (sw : Bool) (u v : Bool) : Bool :=
  if sw then applyKind op v u else applyKind op u v

theorem pair_collision (A B : Kind) : ∀ (sa sb : Bool),
    ∃ a b c d : Bool, (a,b)≠(c,d) ∧
      pairCode A sa a b=pairCode A sa c d ∧ pairCode B sb a b=pairCode B sb c d := by
  cases A <;> cases B <;> decide

theorem joint_reader_code {ρ : Type} (x y : ρ→Bool) (different : x≠y) (g : TraceGate ρ)
    (rx : reads g x) (ry : reads g y) :
    ∃ sw : Bool, ∀ i, g.value i=pairCode g.kind sw (x i) (y i) := by
  rcases rx with xl|xr <;> rcases ry with yl|yr
  · exact (different (xl.symm.trans yl)).elim
  · exact ⟨false,by simp [TraceGate.value,pairCode,xl,yr]⟩
  · exact ⟨true,by simp [TraceGate.value,pairCode,xr,yl]⟩
  · exact (different (xr.symm.trans yr)).elim

theorem two_joint_readers_impossible {ρ τ : Type} (x y out : ρ→Bool)
    (raw : List (ρ→Bool)) (gs : List (TraceGate ρ)) (A B : TraceGate ρ)
    (rxA : reads A x) (ryA : reads A y) (rxB : reads B x) (ryB : reads B y)
    (different : x≠y) (notPrimary : out≠x ∧ out≠y)
    (well : registered raw gs) (available : out∈traceWires raw gs)
    (point : Bool→Bool→τ→ρ)
    (px : ∀ a b j, x (point a b j)=a)
    (py : ∀ a b j, y (point a b j)=b)
    (fixed : ∀ a b c d j, agreeOutside (fun f => f=x ∨ f=y) (point a b j) (point c d j) raw)
    (separate : ∀ a b c d : Bool, (a,b)≠(c,d) → ∃ j : τ, out (point a b j)≠out (point c d j)) :
    ∃ g∈gs, (reads g x ∨ reads g y) ∧ g≠A ∧ g≠B := by
  classical
  obtain ⟨sa,saCode⟩ := joint_reader_code x y different A rxA ryA
  obtain ⟨sb,sbCode⟩ := joint_reader_code x y different B rxB ryB
  obtain ⟨a,b,c,d,ne,ca,cb⟩ := pair_collision A.kind B.kind sa sb
  obtain ⟨j,away⟩ := separate a b c d ne
  have eA : A.value (point a b j)=A.value (point c d j) := by
    simpa only [saCode,px,py] using ca
  have eB : B.value (point a b j)=B.value (point c d j) := by
    simpa only [sbCode,px,py] using cb
  have badOut : ¬(out=x ∨ out=y) := fun e => e.elim notPrimary.1 notPrimary.2
  obtain ⟨g,hg,read,diff⟩ := reader_witness (fun f => f=x ∨ f=y) _ _ well
    (fixed a b c d j) available badOut away
  refine ⟨g,hg,?_,fun eq => diff (eq ▸ eA),fun eq => diff (eq ▸ eB)⟩
  rcases read with (h|h)|(h|h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

end CoThetaFreeCore


namespace CoPetersenThetaGeometry

def nine (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def embedding (j : Fin 6) : List Nat := match j.val with
  | 0 => [2, 8, 3, 1, 6, 7, 5]
  | 1 => [3, 5, 8, 2, 7, 4, 0]
  | 2 => [8, 0, 5, 3, 4, 6, 1]
  | 3 => [5, 1, 0, 8, 6, 7, 2]
  | 4 => [0, 2, 1, 5, 7, 4, 3]
  | _ => [1, 3, 2, 0, 4, 6, 8]

def cycleEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | _ => 5

def subEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 4
  | 1 => 6
  | 2 => 7
  | 3 => 4
  | 4 => 6
  | _ => 7

def outerNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | _ => 0

def shortNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | _ => 2

def sensitive : List Nat := [2, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 4, 1, 1, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 2, 9, 8, 2, 2, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 4, 5, 4, 18, 16, 4, 4, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 8, 1, 1, 10, 1, 5, 1, 8, 1, 0, 1, 40, 1, 65, 1, 129, 1, 257, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 1, 0, 1, 65, 1, 128, 1, 256, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 2, 0, 2, 130, 2, 256, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 4, 0, 4, 260, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 8, 0]

def plant (j : Fin 6) (m : Nat) : Nat :=
  (List.range 7).foldl (fun val i => if m.testBit i then
    val ||| (1 <<< ((embedding j).getD i 0)) else val) 0

theorem theta_slice : ∀ (j : Fin 6) (r : Fin 128),
    nine (plant j r.val) = theta r.val ∧
    (plant j r.val).testBit (cycleEnd j)=false ∧
    (plant j r.val).testBit (subEnd j)=false := by decide +kernel

theorem every_input_has_slice : ∀ v : Fin 9, ∃ j : Fin 6,
    cycleEnd j=v.val ∨ subEnd j=v.val := by decide

def sensRow (p q : Fin 9) (v : Bool) : Nat :=
  sensitive.getD (2*(9*p.val+q.val)+v.toNat) 0

theorem sensitive_at_both : ∀ (p q : Fin 9), p≠q → ∀ v : Bool,
    let r := sensRow p q v
    r.testBit p.val=false ∧ r.testBit q.val=v ∧
    nine r=false ∧ nine (r ||| (1 <<< p.val))=true := by decide +kernel

def panel (p q : Bool) : Bool × Bool × Bool := (p&&q,(p&&q)||p,(p&&q)||q)

theorem slice_panels : ∀ (j : Fin 6) (p q : Bool),
    let r := (if p then 1 <<< cycleEnd j else 0) ||| (if q then 1 <<< subEnd j else 0)
    (nine r, nine (r ||| (1 <<< outerNeighbor j)), nine (r ||| (1 <<< shortNeighbor j))) = panel p q := by
  decide +kernel

inductive Kind where | conj | disj | leftOnly | rightOnly
def binary : Kind → Bool → Bool → Bool
  | .conj,a,b => a&&b
  | .disj,a,b => a||b
  | .leftOnly,a,b => a && !b
  | .rightOnly,a,b => !a && b

theorem unbalanced_code (kind : Kind) : ∀ (a b c d : Bool),
    ¬[(binary kind false false,a),(binary kind false true,b),
      (binary kind true false,c),(binary kind true true,d)].Nodup := by
  cases kind <;> decide

end CoPetersenThetaGeometry
namespace CoThetaNine
open CoThetaFreeCore
open CoPetersenThetaGeometry (nine sensRow cycleEnd subEnd outerNeighbor shortNeighbor)

abbrev Input := Fin 512
def vtx (i : Fin 9) (r : Input) : Bool := r.val.testBit i.val
def ans (r : Input) : Bool := nine r.val
def vertices : List (Input→Bool) := absentBit::List.ofFn vtx

def row (n : Nat) : Input := ⟨n % 512,Nat.mod_lt _ (by decide)⟩
def index (n : Nat) : Fin 9 := ⟨n % 9,Nat.mod_lt _ (by decide)⟩
def ep (j : Fin 6) := index (cycleEnd j)
def eqp (j : Fin 6) := index (subEnd j)
def low (p q : Fin 9) (v : Bool) : Input := row (sensRow p q v)
def high (p q : Fin 9) (v : Bool) : Input := row ((low p q v).val ||| (1 <<< p.val))

theorem sens_data : ∀ (p q : Fin 9), p≠q → ∀ b : Bool,
    vtx p (low p q b)=false ∧ vtx p (high p q b)=true ∧
    vtx q (low p q b)=b ∧ vtx q (high p q b)=b ∧
    ans (low p q b)≠ans (high p q b) ∧
    ∀ t : Fin 9, t≠p → vtx t (low p q b)=vtx t (high p q b) := by decide +kernel

theorem distinct_raw : ∀ i j : Fin 9, i≠j → ∃ r : Input, vtx i r≠vtx j r := by
  decide +kernel

theorem not_raw : ∀ i : Fin 9, ∃ r : Input, ans r≠vtx i r := by decide +kernel

theorem distinct_inputs {i j : Fin 9} (ne : i≠j) : vtx i≠vtx j := by
  obtain ⟨r,d⟩ := distinct_raw i j ne
  exact fun h => d (congrFun h r)

theorem not_input (i : Fin 9) : ans≠vtx i := by
  obtain ⟨r,d⟩ := not_raw i
  exact fun h => d (congrFun h r)

theorem agree_on_vertices (E : (Input→Bool)→Prop) (r s : Input)
    (ok : ∀ i : Fin 9, ¬E (vtx i) → vtx i r=vtx i s) :
    agreeOutside E r s vertices := by
  intro w hw h
  rcases List.mem_cons.mp hw with z|h2
  · subst w
    rfl
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h2
    subst w
    exact ok i h

def point (j : Fin 6) (a b : Bool) (t : Fin 3) : Input :=
  let u := (if a then 1 <<< cycleEnd j else 0) ||| (if b then 1 <<< subEnd j else 0)
  row (match t.val with
    | 0 => u
    | 1 => u ||| (1 <<< outerNeighbor j)
    | _ => u ||| (1 <<< shortNeighbor j))

theorem panel_data : ∀ (j : Fin 6), ep j≠eqp j ∧
    (∀ a b t, vtx (ep j) (point j a b t)=a ∧ vtx (eqp j) (point j a b t)=b) ∧
    (∀ a b c d t, ∀ i : Fin 9, i≠ep j → i≠eqp j →
      vtx i (point j a b t)=vtx i (point j c d t)) ∧
    (∀ a b c d : Bool, (a,b)≠(c,d) → ∃ t : Fin 3, ans (point j a b t)≠ans (point j c d t)) := by
  decide +kernel

theorem third_joint_reader (j : Fin 6) (gs : List (TraceGate Input)) (A B : TraceGate Input)
    (rxA : reads A (vtx (ep j))) (ryA : reads A (vtx (eqp j)))
    (rxB : reads B (vtx (ep j))) (ryB : reads B (vtx (eqp j)))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, (reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) ∧ g≠A ∧ g≠B := by
  obtain ⟨distinct,axis,other,apart⟩ := panel_data j
  apply two_joint_readers_impossible (vtx (ep j)) (vtx (eqp j)) ans vertices gs A B
    rxA ryA rxB ryB (distinct_inputs distinct) ⟨not_input _,not_input _⟩ well out
    (point j) (fun a b t => (axis a b t).1) (fun a b t => (axis a b t).2) _ apart
  intro a b c d t
  apply agree_on_vertices
  intro i ni
  exact other a b c d t i (fun e => ni (Or.inl (congrArg vtx e)))
    (fun e => ni (Or.inr (congrArg vtx e)))

theorem masks_some_value (op : CoThetaFreeCore.Kind) : ∀ sw : Bool, ∃ v : Bool,
    ∀ a b : Bool, pairCode op sw a v=pairCode op sw b v := by
  cases op <;> decide

theorem another_raw_reader {p q : Fin 9} (ne : p≠q) (gs : List (TraceGate Input))
    (gate : TraceGate Input) (rx : reads gate (vtx p)) (ry : reads gate (vtx q))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) ∧ g≠gate := by
  obtain ⟨sw,code⟩ := joint_reader_code _ _ (distinct_inputs ne) gate rx ry
  obtain ⟨b,masked⟩ := masks_some_value gate.kind sw
  obtain ⟨pl,ph,ql,qh,diff,fixed⟩ := sens_data p q ne b
  have source : agreeOutside (fun w => w=vtx p) (low p q b) (high p q b) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fixed i (fun e => ni (congrArg vtx e))
  have mask : gate.value (low p q b)=gate.value (high p q b) := by
    simpa only [code,pl,ph,ql,qh] using masked false true
  exact second_reader (vtx p) (low p q b) (high p q b) gate well source out (not_input p) diff mask

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def neighborIndex (p : Fin 9) := index (p.val+1)
theorem neighbor_diff : ∀ p : Fin 9, p≠neighborIndex p := by decide

theorem a_raw_reader (p : Fin 9) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) := by
  let q := neighborIndex p
  have ne : p≠q := neighbor_diff p
  obtain ⟨_,_,_,_,diff,fix⟩ := sens_data p q ne false
  have source : agreeOutside (fun w => w=vtx p) (low p q false) (high p q false) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fix i (fun e => ni (congrArg vtx e))
  obtain ⟨g,hg,h,_⟩ := reader_witness (·=vtx p) _ _ well source out (not_input p) diff
  exact ⟨g,hg,h⟩

def ThreeReaders {ρ : Type} (P : TraceGate ρ→Prop) (gs : List (TraceGate ρ)) : Prop :=
  ∃ A∈gs, ∃ B∈gs, ∃ C∈gs, P A ∧ P B ∧ P C ∧ A≠B ∧ A≠C ∧ B≠C

theorem three_for_pair (j : Fin 6) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs)
    (known : (∃ A∈gs, ∃ B∈gs, reads A (vtx (ep j)) ∧ reads B (vtx (ep j)) ∧ A≠B) ∨
             (∃ A∈gs, ∃ B∈gs, reads A (vtx (eqp j)) ∧ reads B (vtx (eqp j)) ∧ A≠B)) :
    ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs := by
  classical
  have ne := (panel_data j).1
  by_cases shared : ∃ J∈gs, reads J (vtx (ep j)) ∧ reads J (vtx (eqp j))
  · obtain ⟨J,hJ,Jp,Jq⟩ := shared
    obtain ⟨A,hA,Ap,AJ⟩ := another_raw_reader ne gs J Jp Jq well out
    obtain ⟨B,hB,Bq,BJ⟩ := another_raw_reader ne.symm gs J Jq Jp well out
    by_cases e : A=B
    · subst B
      obtain ⟨C,hC,read,CJ,CA⟩ := third_joint_reader j gs J A Jp Jq Ap Bq well out
      exact ⟨J,hJ,A,hA,C,hC,Or.inl Jp,Or.inl Ap,read,AJ.symm,CJ.symm,CA.symm⟩
    · exact ⟨J,hJ,A,hA,B,hB,Or.inl Jp,Or.inl Ap,Or.inr Bq,AJ.symm,BJ.symm,e⟩
  · rcases known with ⟨A,hA,B,hB,Ap,Bp,AB⟩|⟨A,hA,B,hB,Aq,Bq,AB⟩
    · obtain ⟨C,hC,Cq⟩ := a_raw_reader (eqp j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inl Ap,Or.inl Bp,Or.inr Cq,AB,
        fun e => shared ⟨A,hA,Ap,e ▸ Cq⟩,fun e => shared ⟨B,hB,Bp,e ▸ Cq⟩⟩
    · obtain ⟨C,hC,Cp⟩ := a_raw_reader (ep j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inr Aq,Or.inr Bq,Or.inl Cp,AB,
        fun e => shared ⟨A,hA,e ▸ Cp,Aq⟩,fun e => shared ⟨B,hB,e ▸ Cp,Bq⟩⟩

end CoThetaNine
namespace CoThetaFreeCore

theorem fresh_ports {ρ : Type} {ws : List (ρ→Bool)} (g : TraceGate ρ)
    (hl : g.left∈ws) (hr : g.right∈ws) (hz : absentBit∈ws) (fresh : g.value∉ws) :
    g.left≠absentBit ∧ g.right≠absentBit ∧ g.left≠g.right := by
  refine ⟨?_,?_,?_⟩
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_left g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_right g.kind g.left with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hl
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases same_result g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz

noncomputable def vanishing {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :=
  gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))

theorem saved_eq_length {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    saved lift gs = (vanishing lift gs).length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [saved,vanishing,h] at * <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

theorem endpoint_in_slice : ∀ p : Fin 9, ∃ j : Fin 6, p=ep j ∨ p=eqp j := by decide

theorem ans_not_zero : ans≠absentBit := by
  intro e
  have bad := congrFun e (row 3)
  have test : ans (row 3)=true := by decide
  exact Bool.noConfusion (test.symm.trans bad)

theorem fresh_slice_head {g : TraceGate Input} {tail : List (TraceGate Input)}
    (h : sufficient vertices ans (g::tail)) (fresh : freshTrace vertices (g::tail)) :
    ∃ j : Fin 6, ThreeReaders (fun t => reads t (vtx (ep j)) ∨ reads t (vtx (eqp j))) (g::tail) := by
  obtain ⟨nonL,nonR,different⟩ := fresh_ports g h.1.1 h.1.2.1 (List.mem_cons_self) fresh.1
  have rawL := (List.mem_cons.mp h.1.1).resolve_left nonL
  have rawR := (List.mem_cons.mp h.1.2.1).resolve_left nonR
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp rawL
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp rawR
  have xy : x≠y := fun eq => different (ex.symm.trans ((congrArg vtx eq).trans ey))
  have rx : reads g (vtx x) := Or.inl ex.symm
  have ry : reads g (vtx y) := Or.inr ey.symm
  obtain ⟨s,hs,sx,other⟩ := another_raw_reader xy _ g rx ry h.1 h.2
  obtain ⟨j,side⟩ := endpoint_in_slice x
  refine ⟨j,three_for_pair j h.1 h.2 ?_⟩
  rcases side with eq|eq
  · exact Or.inl ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩
  · exact Or.inr ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩

theorem nonempty_solution {gs : List (TraceGate Input)} (h : sufficient vertices ans gs) : gs≠[] := by
  intro e
  subst gs
  have m : ans∈vertices := h.2
  rcases List.mem_cons.mp m with z|r
  · exact ans_not_zero z
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp r
    exact not_input i eq.symm

end CoThetaNine
namespace CoThetaBits
open CoThetaFreeCore

abbrev Width := 440
abbrev Bits := BitVec Width
abbrev Wire := Bits × Bits
abbrev Row := Bool × Fin Width
def zero : Wire := (0,0)
def full : Bits := BitVec.allOnes Width
def target : Wire := (full,0)

def den (wire : Wire) (r : Row) : Bool :=
  (if r.1 then wire.1 else wire.2).getLsbD r.2.val

def gate : Kind → Wire → Wire → Wire
  | .conj,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .disj,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .leftOnly,a,b => (a.1 &&& ~~~b.1,a.2 &&& ~~~b.2)
  | .rightOnly,a,b => (~~~a.1 &&& b.1,~~~a.2 &&& b.2)

theorem den_injective {a b : Wire} (h : den a=den b) : a=b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (true,⟨i,hi⟩)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (false,⟨i,hi⟩)

theorem den_gate (kind : Kind) (a b : Wire) :
    den (gate kind a b) = fun i => applyKind kind (den a i) (den b i) := by
  funext r
  obtain ⟨side,i⟩ := r
  cases kind <;> cases side <;>
    simp [den,gate,applyKind,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,i.isLt]

theorem den_zero : den zero = absentBit := by
  funext r
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,zero,absentBit]

theorem den_target (r : Row) : den target r = r.1 := by
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,target,full,BitVec.getLsbD_allOnes,i.isLt]

def sep (w : Wire) : Bits := w.1 ^^^ w.2

def coverage : List Wire → Bits
  | [] => 0
  | w::ws => sep w ||| coverage ws

theorem bit_covered {l : List Wire} {w : Wire} (hw : w∈l) (i : Fin Width)
    (h : den w (true,i) ≠ den w (false,i)) : (coverage l).getLsbD i.val=true := by
  induction l with
  | nil => simp at hw
  | cons a xs ih =>
    rw [coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp hw with e|mem
    · subst a
      have hd : w.1.getLsbD i.val ≠ w.2.getLsbD i.val := h
      simp only [sep,BitVec.getLsbD_xor]
      cases hp : w.1.getLsbD i.val <;> cases hn : w.2.getLsbD i.val <;> simp_all
    · simp [ih mem]

theorem live_coverage {k} {S : (Row → Bool) → Prop} (l : List Wire)
    (h : Live (den target) k S) (sub : ∀ w, S w → ∃ v∈l, den v=w) :
    coverage l = full := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin Width := ⟨i,hi⟩
  have ne : den target (true,j) ≠ den target (false,j) := by simp [den_target]
  obtain ⟨w,hw,hd⟩ := h.separates (true,j) (false,j) ne
  obtain ⟨v,hv,eq⟩ := sub w hw
  have h1 := bit_covered hv j (eq.symm ▸ hd)
  simpa [full,BitVec.getLsbD_allOnes,hi,j] using h1

end CoThetaBits

namespace CoThetaFreeCore

theorem length_of_cover {α : Type} (xs ys : List α) (nd : xs.Nodup)
    (sub : ∀ a∈xs, a∈ys) : xs.length≤ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have parts := List.nodup_cons.mp nd
    have has : a∈ys := sub a (by simp)
    have hl := erase_len a ys has
    have nextOK : xs.length≤(eraseOnce a ys).length := ih (eraseOnce a ys) parts.2 (by
      intro x hx
      have ne : x≠a := fun eq => parts.1 (eq ▸ hx)
      exact erase_preserves ne ys (sub x (List.mem_cons_of_mem _ hx)))
    simp only [List.length_cons]
    omega

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

def Rep (ws : List Wire) (S : (Row→Bool)→Prop) : Prop :=
  ∀ f, S f ↔ ∃ w∈ws, den w=f

private theorem mem_rep {S ws} (rep : Rep ws S) (w : Wire) : w∈ws ↔ S (den w) := by
  constructor
  · intro h
    exact (rep _).2 ⟨w,h,rfl⟩
  · intro h
    obtain ⟨v,hv,e⟩ := (rep _).1 h
    exact den_injective e ▸ hv

private theorem den_nodup {ws : List Wire} (nd : ws.Nodup) : (ws.map den).Nodup := by
  induction ws with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp nd with ⟨hne,ht⟩
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih ht⟩
    intro hm
    obtain ⟨v,hv,e⟩ := List.mem_map.mp hm
    exact hne (den_injective e ▸ hv)

theorem state_width {k S ws} (h : Live (den target) k S) (nd : ws.Nodup) (rep : Rep ws S) :
    ws.length≤k+1 := by
  obtain ⟨xs,hsize,hsub⟩ := h.width_cover
  have le := length_of_cover (ws.map den) xs (den_nodup nd) (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hf
    exact hsub f ((rep _).2 ⟨w,hw,eq⟩))
  simpa using Nat.le_trans le hsize

def trim (a b : Wire) (ws : List Wire) : List Wire :=
  ws.filter (fun w => w != a && w != b)

theorem mem_trim {w a b : Wire} {ws : List Wire} :
    w∈trim a b ws ↔ w∈ws ∧ w≠a ∧ w≠b := by simp [trim]

def allKinds : List Kind := [.conj,.disj,.leftOnly,.rightOnly]
def options (a b : Wire) : List (List Wire) := [[],[a],[b],[a,b]]

def testStep (k : Nat) (ws : List Wire) (nextOK : List Wire → Bool) : Bool :=
  ws.any fun a => ws.any fun b => a != b &&
    (allKinds.any fun kind =>
      let z := gate kind a b
      z != zero && !(ws.contains z) &&
        (options a b).any fun keep =>
          let out := z::(keep++trim a b ws)
          out.length≤k+1 && coverage out==full && nextOK out)

def certifiedSearch : Nat → List Wire → Bool
  | 0, ws => ws.contains target
  | k+1, ws => ws.contains target || (ws.length≤k+2 && testStep k ws (certifiedSearch k))

theorem step_hit {k ws nextOK a b keep kind} (ha : a∈ws) (hb : b∈ws)
    (ab : a≠b) (hk : keep∈options a b)
    (non : gate kind a b ≠zero) (fresh : gate kind a b∉ws)
    (len : (gate kind a b::(keep++trim a b ws)).length≤k+1)
    (cov : coverage (gate kind a b::(keep++trim a b ws))=full)
    (valid : nextOK (gate kind a b::(keep++trim a b ws))=true) : testStep k ws nextOK=true := by
  have hkind : kind∈allKinds := by cases kind <;> simp [allKinds]
  unfold testStep
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  simp only [Bool.and_eq_true,bne_iff_ne,ab,true_and,List.any_eq_true,Bool.not_eq_true']
  refine ⟨ab,kind,hkind,?_⟩
  simp [non,fresh]
  have ct : keep.length + (trim a b ws).length ≤ k := by
    simp only [List.length_cons,List.length_append] at len
    omega
  exact ⟨keep,hk,by simp [ct,cov,valid]⟩

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

noncomputable def kept (a b : Wire) (U : (Row→Bool)→Prop) : List Wire := by
  classical
  exact (if U (den a) then [a] else []) ++ (if U (den b) then [b] else [])

theorem is_option (a b : Wire) (U : (Row→Bool)→Prop) : kept a b U∈options a b := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,options,p,q]

theorem mem_kept {v a b : Wire} {U : (Row→Bool)→Prop} :
    v∈kept a b U ↔ (v=a ∧ U (den a)) ∨ (v=b ∧ U (den b)) := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,p,q]

theorem edit_member {a b v : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    v∈(kept a b U ++ trim a b ws) ↔ U (den v) := by
  classical
  constructor
  · intro hm
    rcases List.mem_append.mp hm with inK | inR
    · rcases mem_kept.mp inK with ⟨e,yes⟩ | ⟨e,yes⟩ <;> subst v <;> exact yes
    · obtain ⟨inside,na,nb⟩ := mem_trim.mp inR
      rcases (mem_rep rep v).1 inside with e | e | hu
      · exact (na (den_injective e)).elim
      · exact (nb (den_injective e)).elim
      · exact hu
  · intro hu
    by_cases ea : v=a
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inl ⟨ea,ea ▸ hu⟩)))
    by_cases eb : v=b
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inr ⟨eb,eb ▸ hu⟩)))
    apply List.mem_append.mpr
    right
    exact mem_trim.mpr ⟨(mem_rep rep v).2 (Or.inr (Or.inr hu)),ea,eb⟩

theorem edit_distinct {a b : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (ab : a≠b) (nd : ws.Nodup) : (kept a b U ++ trim a b ws).Nodup := by
  classical
  have ndr : (trim a b ws).Nodup := nd.filter _
  have ha : a∉trim a b ws := fun h => (mem_trim.mp h).2.1 rfl
  have hb : b∉trim a b ws := fun h => (mem_trim.mp h).2.2 rfl
  by_cases p : U (den a) <;> by_cases q : U (den b) <;>
    simp [kept,p,q,List.nodup_cons,ha,hb,ab,ndr]

theorem edit_rep {a b z : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    Rep (z::(kept a b U ++ trim a b ws)) (ins (den z) U) := by
  intro f
  constructor
  · intro hf
    rcases hf with e | hu
    · exact ⟨z,by simp,e.symm⟩
    · obtain ⟨v,hv,e⟩ := (rep f).1 (Or.inr (Or.inr hu))
      refine ⟨v,List.mem_cons_of_mem _ ((edit_member rep).2 ?_),e⟩
      exact e.symm ▸ hu
  · intro h
    obtain ⟨v,hv,e⟩ := h
    rcases List.mem_cons.mp hv with vz | tail
    · subst v
      exact Or.inl e.symm
    · exact Or.inr (e ▸ (edit_member rep).1 tail)

end CoThetaBits

namespace CoThetaFreeCore
variable {ρ : Type}

theorem Live.excludes_zero {goal : ρ→Bool} {k S} (h : Live goal k S)
    (ng : goal≠absentBit) : ¬S absentBit := by
  induction h with
  | stop => exact fun eq => ng eq.symm
  | step _ _ ha hb _ _ ih =>
    intro bad
    rcases bad with eq | eq | u
    · exact ha eq.symm
    · exact hb eq.symm
    · exact ih (Or.inr u)

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

private theorem target_nonzero : den target≠absentBit := by
  intro eq
  have q := congrFun eq (true,0)
  simp [den_target,absentBit] at q

theorem certified_complete {m S} (run : Live (den target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → certifiedSearch fuel ws=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have ht : target∈ws := (mem_rep rep target).2 rfl
    cases fuel <;> simp [certifiedSearch,ht]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      let out := z::(kept x y U ++ trim x y ws)
      have dg : den z=(fun i => applyKind kind (den x i) (den y i)) := den_gate _ _ _
      have zab : x≠y := fun e => ab (congrArg den e)
      have nz : z≠zero := by
        intro e
        have dz : (fun i => applyKind kind (den x i) (den y i))=absentBit :=
          dg.symm.trans ((congrArg den e).trans den_zero)
        exact tail.excludes_zero target_nonzero (Or.inl dz.symm)
      have nf : z∉ws := by
        intro hz
        have st := (mem_rep rep z).1 hz
        exact fresh (dg ▸ st)
      have nextRep : Rep out (ins (fun i => applyKind kind (den x i) (den y i)) U) := by
        have e := edit_rep (z:=z) rep
        rw [dg] at e
        exact e
      have nextNd : out.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,edit_distinct zab nd⟩
        intro hz
        have inU := (edit_member rep).1 hz
        exact fresh (Or.inr (Or.inr (dg ▸ inU)))
      have width := state_width tail nextNd nextRep
      have cover := live_coverage out tail (fun f hf => (nextRep f).1 hf)
      have verdict := ih k (by omega) out nextNd nextRep
      have stepOk : testStep k ws (certifiedSearch k)=true :=
        step_hit hx hy zab (is_option x y U) nz nf (Nat.le_trans width (by omega)) cover verdict
      have current := Live.step kind ab ha hb fresh tail
      have max := state_width current nd rep
      have size : ws.length≤k+2 := by omega
      simp [certifiedSearch,size,stepOk]

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

def raw : List Wire := [(0xaa1404600a0270047003878002808c017f84fc07ff0fffe0050138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff,0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a),
(0xcc1807800c0380078003f8000300f00181ff3ff807f00ffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000,0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c),
(0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00007fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff,0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0),
(0xffe000000ffffff80000000003fffffe0007fffff800000007fffffc000003fff000000007ffffffffff000000003ffffffffc00000000,0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220),
(0xfffffffff00000000000000003fffffffff800000000000007fffffffffffc000000000007ffffffffffffffffffc00000000000000000,0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0),
(0xfffffffffffffffffffffffffc000000000000000000000007fffffffffffffffffffffff8000000000000000000000000000000000000,0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300),
(0xfffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000,0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00)]

def col (j : Fin 7) : Wire := raw[j.val]?.getD zero
def sample (r : Row) (j : Fin 7) : Bool := den (col j) r
def empty : Row := (false,0)
def start : List (Row→Bool) := (fun _ => false)::(fun _ => true)::raw.map den

def edgeWord : Wire := (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .conj (col 0) (col 2)) (gate .conj (col 1) (col 2))) (gate .conj (col 0) (col 3))) (gate .conj (col 3) (col 4))) (gate .conj (col 1) (col 4))) (gate .conj (col 0) (col 5))) (gate .conj (col 5) (col 6))) (gate .conj (col 1) (col 6)))

theorem edge_exact : edgeWord=target := by decide +kernel
theorem sample_correct (r : Row) : CoThetaFreeCore.theta (sample r)=den target r := by
  have h := congrFun (congrArg den edge_exact) r
  simp only [edgeWord,den_gate,applyKind] at h
  exact h

theorem raw_is_ofFn : List.ofFn col=raw := rfl
theorem raw_nodup : raw.Nodup := by decide +kernel
theorem low_raw : ∀ j : Fin 7, den (col j) empty=false := by decide +kernel

def privateIndex (j : Fin 7) : Fin Width := match j.val with
  | 0 => 4
  | 1 => 17
  | 2 => 1
  | 3 => 35
  | 4 => 71
  | 5 => 148
  | _ => 244

theorem private_row : ∀ j k : Fin 7,
    den (col k) (true,privateIndex j) ≠ den (col k) (false,privateIndex j) → k=j := by decide +kernel

private theorem indexed {v : Wire} (h : v∈raw) : ∃ j, col j=v := by
  rw [←raw_is_ofFn] at h
  exact List.mem_ofFn.mp h

theorem root_rep {k S} (h : Live (den target) k S)
    (inputs : ∀ f, S f → f=absentBit ∨ ∃ j, den (col j)=f) : Rep raw S := by
  have allcol (j : Fin 7) : S (den (col j)) := by
    let i := privateIndex j
    have diff : den target (true,i) ≠ den target (false,i) := by simp [den_target]
    obtain ⟨v,hv,hd⟩ := h.separates (true,i) (false,i) diff
    rcases inputs v hv with z | ⟨l,e⟩
    · subst v
      exact (hd rfl).elim
    · subst v
      obtain rfl := private_row j l hd
      exact hv
  intro f
  constructor
  · intro hf
    rcases inputs f hf with z | ⟨j,eq⟩
    · exact (h.excludes_zero target_nonzero (z ▸ hf)).elim
    · refine ⟨col j,?_,eq⟩
      rw [←raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · rintro ⟨v,hv,eq⟩
    obtain ⟨j,rfl⟩ := indexed hv
    exact eq ▸ allcol j

theorem root_input {f : Row→Bool} (hm : f∈start.map (norm empty)) :
    f=absentBit ∨ ∃ j, den (col j)=f := by
  obtain ⟨v,hin,rfl⟩ := List.mem_map.mp hm
  rcases List.mem_cons.mp hin with e | tail
  · subst v
    exact Or.inl rfl
  rcases List.mem_cons.mp tail with e | t
  · subst v
    exact Or.inl rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp t
  obtain ⟨j,rfl⟩ := indexed hw
  right
  refine ⟨j,?_⟩
  funext r
  simp [CoThetaFreeCore.norm,low_raw j,phase]

theorem no_small_ordinary (certificate : certifiedSearch 10 raw=false)
    {n ws} (program : Ordinary start n ws) (cost : n≤10) (out : den target∈ws) : False := by
  obtain ⟨ys,fre,contains⟩ := simulate_all_wires empty program
  have self : norm empty (den target)=den target := by
    funext r
    simp [CoThetaFreeCore.norm,den_target,empty,phase]
  have hin : den target∈ys := self ▸ contains _ out
  have rn : absentBit∈start.map (norm empty) := by
    change absentBit∈(absentBit::_)
    simp
  obtain ⟨m,S,le,live,sub⟩ :=
    rewind fre rn (Live.stop (goal:=den target)) (fun w eq => eq.symm ▸ hin)
  have rep := root_rep live (fun f hf => root_input (sub f hf))
  have yes := certified_complete live 10 (by omega) raw raw_nodup rep
  exact Bool.false_ne_true (certificate.symm.trans yes)

end CoThetaBits
namespace CoThetaFreeCore

theorem Free.map_rows {ρ σ : Type} (lift : σ→ρ)
    {init ws n} (run : @Free ρ init n ws) :
    Free (init.map (restrict lift)) n (ws.map (restrict lift)) := by
  induction run with
  | start => exact Free.start
  | @binary n ws a b pre kind ha hb ih =>
    have h1 := List.mem_map_of_mem (f:=restrict lift) ha
    have h2 := List.mem_map_of_mem (f:=restrict lift) hb
    exact Free.binary ih kind h1 h2

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7
def sliceLift (j : Fin 6) (r : SmallInput) : Input := row (CoPetersenThetaGeometry.plant j r.val)

def coord7 (j : Fin 6) (v : Fin 9) : Option (Fin 7) :=
  match j.val,v.val with
  | 0,2 => some 0
  | 0,8 => some 1
  | 0,3 => some 2
  | 0,1 => some 3
  | 0,6 => some 4
  | 0,7 => some 5
  | 0,5 => some 6
  | 1,3 => some 0
  | 1,5 => some 1
  | 1,8 => some 2
  | 1,2 => some 3
  | 1,7 => some 4
  | 1,4 => some 5
  | 1,0 => some 6
  | 2,8 => some 0
  | 2,0 => some 1
  | 2,5 => some 2
  | 2,3 => some 3
  | 2,4 => some 4
  | 2,6 => some 5
  | 2,1 => some 6
  | 3,5 => some 0
  | 3,1 => some 1
  | 3,0 => some 2
  | 3,8 => some 3
  | 3,6 => some 4
  | 3,7 => some 5
  | 3,2 => some 6
  | 4,0 => some 0
  | 4,2 => some 1
  | 4,1 => some 2
  | 4,5 => some 3
  | 4,7 => some 4
  | 4,4 => some 5
  | 4,3 => some 6
  | 5,1 => some 0
  | 5,3 => some 1
  | 5,2 => some 2
  | 5,0 => some 3
  | 5,4 => some 4
  | 5,6 => some 5
  | 5,8 => some 6
  | _,_ => none

theorem slice7_values : ∀(j : Fin 6) (r : SmallInput),
    ans (sliceLift j r)=ans7 r ∧ vtx (ep j) (sliceLift j r)=false ∧
    vtx (eqp j) (sliceLift j r)=false ∧
    ∀ i : Fin 9, vtx i (sliceLift j r)=
      match coord7 j i with | none => false | some k => raw7 k r := by decide +kernel

theorem slice_known (j : Fin 6) : ∀ w∈vertices, restrict (sliceLift j) w∈vertices7 := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
    subst w
    cases h : coord7 j i with
    | none =>
      have eq : restrict (sliceLift j) (vtx i)=absentBit := by
        funext r
        simpa [restrict,h,absentBit] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_self
    | some k =>
      have eq : restrict (sliceLift j) (vtx i)=raw7 k := by
        funext r
        simpa [restrict,h] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

def packBits (a b c d e f g : Bool) : SmallInput :=
  ⟨(a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat) % 128,
    Nat.mod_lt _ (by decide)⟩

def pack (x : Fin 7 → Bool) : SmallInput := packBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem pack_exact : ∀ a b c d e f g : Bool,
    let t := packBits a b c d e f g
    (raw7 0 t,raw7 1 t,raw7 2 t,raw7 3 t,raw7 4 t,raw7 5 t,raw7 6 t)=(a,b,c,d,e,f,g) := by
  intro a b c d e f g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem unpack (x : Fin 7→Bool) (j : Fin 7) : raw7 j (pack x)=x j := by
  have h := pack_exact (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  change (_,_,_,_,_,_,_) = (_,_,_,_,_,_,_) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := h
  have total : ∀ t : Fin 7, t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by decide
  rcases total j with e|e|e|e|e|e|e <;> subst j <;> assumption

theorem numeric_goal (r : SmallInput) : ans7 r=CoThetaFreeCore.theta (fun j => raw7 j r) := by
  rfl

def toRows (r : CoThetaBits.Row) := pack (CoThetaBits.sample r)

theorem numeric_target : restrict toRows ans7=CoThetaBits.den CoThetaBits.target := by
  funext r
  change ans7 (toRows r)=_
  rw [numeric_goal]
  have eq : (fun j => raw7 j (toRows r))=CoThetaBits.sample r :=
    funext (unpack (CoThetaBits.sample r))
  rw [eq]
  exact CoThetaBits.sample_correct r

theorem numeric_lower (cert : CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false)
    {n ws} (run : Free vertices7 n ws) (goal : ans7∈ws) : 11≤n := by
  classical
  obtain ⟨m,S,le,live,sub⟩ := rewind (run.map_rows toRows) List.mem_cons_self
    (Live.stop (goal:=CoThetaBits.den CoThetaBits.target)) (by
      intro w e
      have h := List.mem_map_of_mem (f:=restrict toRows) goal
      rw [numeric_target] at h
      exact e ▸ h)
  have rep := CoThetaBits.root_rep live (by
    intro f h
    have w := sub f h
    obtain ⟨g,hg,eq⟩ := List.mem_map.mp w
    subst f
    rcases List.mem_cons.mp hg with z|other
    · subst g
      exact Or.inl rfl
    · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
      subst g
      exact Or.inr ⟨j,funext (fun r => (unpack (CoThetaBits.sample r) j).symm)⟩)
  apply Classical.byContradiction
  intro bad
  have pass := CoThetaBits.certified_complete live 10 (by omega) _ CoThetaBits.raw_nodup rep
  exact Bool.false_ne_true (cert.symm.trans pass)

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

theorem three_saved (j : Fin 6) {gs : List (TraceGate Input)}
    (three : ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs) :
    3≤saved (sliceLift j) gs := by
  classical
  obtain ⟨A,hA,B,hB,C,hC,rA,rB,rC,AB,AC,BC⟩ := three
  have zp : restrict (sliceLift j) (vtx (ep j))=absentBit :=
    funext (fun r => (slice7_values j r).2.1)
  have zq : restrict (sliceLift j) (vtx (eqp j))=absentBit :=
    funext (fun r => (slice7_values j r).2.2.1)
  have retain (g : TraceGate Input) (hg : g∈gs) (r : reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) :
      g∈vanishing (sliceLift j) gs := by
    have d : disappears (sliceLift j) g := r.elim (reading_zero_disappears _ zp) (reading_zero_disappears _ zq)
    simp [vanishing,hg,d]
  have nd : [A,B,C].Nodup := by simp [AB,AC,BC]
  have sub : ∀ t∈[A,B,C],t∈vanishing (sliceLift j) gs := by
    intro t h
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain A hA rA
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain B hB rB
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain C hC rC
    · simp at h
  rw [saved_eq_length]
  exact length_of_cover [A,B,C] _ nd sub

theorem residual_at_least_eleven (cert : SignedLower)
    (j : Fin 6) {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) :
    11≤remaining (sliceLift j) gs := by
  obtain ⟨ws,run,sub⟩ := restrict_trace (sliceLift j) gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self (slice_known j)
  have read := sub ans ok.2
  have ax : restrict (sliceLift j) ans=ans7 := funext (fun r => (slice7_values j r).1)
  rw [ax] at read
  simpa only [Nat.zero_add] using cert run read

theorem any_nine_lower (cert : SignedLower)
    {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) : 14≤gs.length := by
  classical
  obtain ⟨ts,solves,fresh,le,_⟩ := simplify_trace gs ok
  cases ts with
  | nil => exact (nonempty_solution solves rfl).elim
  | cons g tail =>
    obtain ⟨j,readers⟩ := fresh_slice_head solves fresh
    have gain := three_saved j readers
    have cost := residual_at_least_eleven cert j solves
    have eq := accounted (sliceLift j) (g::tail)
    omega

end CoThetaNine
namespace CoNatBench
abbrev Word := Nat × Nat
def project (w : CoThetaBits.Wire) : Word := (w.1.toNat,w.2.toNat)
def target := project CoThetaBits.target
def all := target.1
def sep (w : Word) := w.1 ^^^ w.2
def meet (a b : Word) : Word := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1,a.2 ||| b.2)
def skip (a b : Word) : Word := (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
def cover (ws : List Word) := ws.foldl (fun c w => c ||| sep w) 0
def pairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | x::xs => xs.any (f x) || pairs f xs
def successors (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  pairs (fun a b =>
    let rest := ws.filter (fun w => w != a && w != b)
    let base := cover rest
    let ca := base ||| sep a
    let cb := base ||| sep b
    let stay := n+1≤k+1
    let half := n≤k+1
    ([meet a b,join a b,skip a b,skip b a] : List Word).any fun z =>
      z != (0,0) && !(ws.contains z) &&
        (let cut := sep z
         ((base ||| cut)==all && next (z::rest)) ||
         (half && (ca ||| cut)==all && next (z::a::rest)) ||
         (half && (cb ||| cut)==all && next (z::b::rest)) ||
         (stay && next (z::a::b::rest)))) ws


def search : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || successors k (search k) ws
end CoNatBench
namespace CoNatBench

def multiplicities : List Word → Nat×Nat
  | [] => (0,0)
  | w::ws =>
    let s := sep w
    let m := multiplicities ws
    (s ||| m.1, (s &&& m.1) ||| m.2)

def guarded (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  let bucket := multiplicities ws
  let once := bucket.1 ^^^ bucket.2
  let cols := ws.map fun w => (w,sep w &&& once)
  let half := n≤k+1
  let stay := n≤k
  pairs (fun a b =>
    let a0 := (a.2 &&& b.1.1)==0
    let a1 := (a.2 &&& b.1.1)==a.2
    let b0 := (b.2 &&& a.1.1)==0
    let b1 := (b.2 &&& a.1.1)==b.2
    let rest := ws.filter (fun w => w != a.1 && w != b.1)
    let base := cover rest
    let attempt (oka okb : Bool) (value : Unit → Word) :=
      (stay || (half && (oka || okb)) || (oka && okb)) &&
        (let z := value ()
         z != (0,0) && !(ws.contains z) &&
          ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
           (half && okb && next (z::a.1::rest)) ||
           (half && oka && next (z::b.1::rest)) ||
           (stay && next (z::a.1::b.1::rest))))
    attempt a1 b1 (fun _ => meet a.1 b.1) ||
      attempt a0 b0 (fun _ => join a.1 b.1) ||
      attempt a0 b1 (fun _ => skip a.1 b.1) ||
      attempt a1 b0 (fun _ => skip b.1 a.1)) cols

def guardedSearch : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || guarded k (guardedSearch k) ws

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

private theorem foldBits (ws : List Word) (i : Nat) (seed : Nat) :
    (ws.foldl (fun c w => c ||| sep w) seed).testBit i =
    (seed.testBit i || ws.any (fun w => (sep w).testBit i)) := by
  induction ws generalizing seed with
  | nil => simp
  | cons a xs ih =>
    simp [List.foldl_cons,ih,Nat.testBit_or,Bool.or_assoc]

theorem covered_iff (ws : List Word) (i : Nat) :
    (cover ws).testBit i=true ↔ ∃ w∈ws,(sep w).testBit i=true := by
  simp [cover,foldBits,List.any_eq_true]

private theorem firstMask (ws : List Word) (i : Nat) (w : Word)
    (h : w∈ws) (bit : (sep w).testBit i=true) : (multiplicities ws).1.testBit i=true := by
  induction ws with
  | nil => simp at h
  | cons a xs ih =>
    change (sep a ||| (multiplicities xs).1).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp h with e|h
    · exact Or.inl (e ▸ bit)
    · exact Or.inr (ih h)

private theorem secondMask (ws : List Word) (i : Nat) {a b : Word} (ab : a≠b)
    (ha : a∈ws) (hb : b∈ws) (da : (sep a).testBit i=true) (db : (sep b).testBit i=true) :
    (multiplicities ws).2.testBit i=true := by
  induction ws with
  | nil => simp at ha
  | cons h xs ih =>
    change ((sep h &&& (multiplicities xs).1) ||| (multiplicities xs).2).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    by_cases x : a=h
    · subst h
      have bt := (List.mem_cons.mp hb).resolve_left ab.symm
      exact Or.inl (by simp [Nat.testBit_and,da,firstMask xs i b bt db])
    · have atail := (List.mem_cons.mp ha).resolve_left x
      by_cases y : b=h
      · subst h
        exact Or.inl (by simp [Nat.testBit_and,db,firstMask xs i a atail da])
      · exact Or.inr (ih atail ((List.mem_cons.mp hb).resolve_left y))

def privateMask (ws : List Word) (a : Word) :=
  sep a &&& ((multiplicities ws).1 ^^^ (multiplicities ws).2)

theorem private_only {ws : List Word} {a : Word} (ha : a∈ws) {i : Nat}
    (h : (privateMask ws a).testBit i=true) :
    (sep a).testBit i=true ∧ ∀ b∈ws, b≠a → (sep b).testBit i=false := by
  simp only [privateMask,Nat.testBit_and,Nat.testBit_xor,Bool.and_eq_true] at h
  obtain ⟨bit,one⟩ := h
  have first := firstMask ws i a ha bit
  have no : (multiplicities ws).2.testBit i=false := by
    cases m : (multiplicities ws).2.testBit i <;> simp_all
  refine ⟨bit,?_⟩
  intro b hb diff
  cases d : (sep b).testBit i with
  | false => rfl
  | true => exact Bool.noConfusion (no.symm.trans (secondMask ws i diff hb ha d bit))

def wordGate : Kind→Word→Word→Word
  | .conj => meet
  | .disj => join
  | .leftOnly => skip
  | .rightOnly => fun a b => skip b a

def leftNeeds : Kind→Bool
  | .conj | .rightOnly => true
  | .disj | .leftOnly => false

theorem bit_rule (op : Kind) (a b : Word) (i : Nat) :
    (wordGate op a b).1.testBit i = applyKind op (a.1.testBit i) (b.1.testBit i) ∧
    (wordGate op a b).2.testBit i = applyKind op (a.2.testBit i) (b.2.testBit i) := by
  cases op <;> simp only [wordGate,meet,join,skip,applyKind,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
  all_goals
    cases a.1.testBit i <;> cases b.1.testBit i <;> cases a.2.testBit i <;> cases b.2.testBit i <;> decide

theorem masked_l (op : Kind) (a b u : Bool) (miss : u≠leftNeeds op) :
    applyKind op a u = applyKind op b u := by
  cases op <;> cases u <;> simp_all [leftNeeds,applyKind]

theorem needed_bit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a)
    {i : Nat} (p : (privateMask ws a).testBit i=true) :
    b.1.testBit i = leftNeeds op := by
  obtain ⟨da,only⟩ := private_only ha p
  have db := only b hb ab.symm
  have beq : b.1.testBit i=b.2.testBit i := by
    simp only [sep,Nat.testBit_xor] at db
    cases hl : b.1.testBit i <;> cases hr : b.2.testBit i <;> simp_all
  have on := (covered_iff ws i).2 ⟨a,ha,da⟩
  rw [←same] at on
  obtain ⟨w,hw,good⟩ := (covered_iff out i).1 on
  rcases others w hw with e|⟨belongs,no⟩
  · subst w
    apply Classical.byContradiction
    intro neg
    obtain ⟨lo,hi⟩ := bit_rule op a b i
    have flat := masked_l op (a.1.testBit i) (a.2.testBit i) (b.1.testBit i) neg
    rw [←beq] at hi
    simp [sep,Nat.testBit_xor,lo,hi,flat] at good
  · exact Bool.noConfusion ((only w belongs no).symm.trans good)

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def maskOK (word mask : Nat) (want : Bool) : Bool :=
  if want then (mask &&& word)==mask else (mask &&& word)==0

theorem mask_hit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  have key := fun i => @needed_bit ws out a b ha hb ab op same others i
  cases d : leftNeeds op with
  | false =>
    simp only [maskOK,Bool.false_eq_true,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]
  | true =>
    simp only [maskOK,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]

def reflectOp : Kind→Kind
  | .conj => .conj
  | .disj => .disj
  | .leftOnly => .rightOnly
  | .rightOnly => .leftOnly

theorem gate_swap (op : Kind) (a b : Word) : wordGate (reflectOp op) b a=wordGate op a b := by
  cases op <;> simp [reflectOp,wordGate,meet,join,skip,Nat.and_comm,Nat.or_comm]

def restOf (ws : List Word) (a b : Word) := ws.filter (fun w => w != a && w != b)
def keepList (ka kb : Bool) (a b : Word) := (if ka then [a] else [])++(if kb then [b] else [])
def extension (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) :=
  wordGate op a b::(keepList ka kb a b ++ restOf ws a b)

theorem rest_mem {ws : List Word} {a b w} : w∈restOf ws a b ↔ w∈ws ∧ w≠a ∧ w≠b := by
  simp [restOf]

theorem kept_mask_left {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (kb : Bool)
    (full : cover (extension ws a b op false kb)=cover ws) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  apply mask_hit ha hb ab op full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl eq
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases kb <;> simp [keepList] at hk
      exact hk ▸ And.intro hb ab.symm
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.1⟩

theorem kept_mask_right {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (ka : Bool)
    (full : cover (extension ws a b op ka false)=cover ws) :
    maskOK a.1 (privateMask ws b) (leftNeeds (reflectOp op))=true := by
  apply mask_hit hb ha ab.symm (reflectOp op) full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl (eq.trans (gate_swap op a b).symm)
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases ka <;> simp [keepList] at hk
      exact hk ▸ And.intro ha ab
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.2⟩

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def tryField (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind) : Bool :=
  let n := ws.length
  let half := n≤k+1
  let stay := n≤k
  let rest := restOf ws a.1 b.1
  let base := cover rest
  let oka := maskOK b.1.1 a.2 (leftNeeds op)
  let okb := maskOK a.1.1 b.2 (leftNeeds (reflectOp op))
  (stay || (half && (oka || okb)) || (oka && okb)) &&
    (let z := wordGate op a.1 b.1
     z != (0,0) && !(ws.contains z) &&
      ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
       (half && okb && next (z::a.1::rest)) ||
       (half && oka && next (z::b.1::rest)) ||
       (stay && next (z::a.1::b.1::rest))))

def pairTry (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) : Bool :=
  tryField k next ws a b .conj || tryField k next ws a b .disj ||
    tryField k next ws a b .leftOnly || tryField k next ws a b .rightOnly

theorem guarded_eq (k : Nat) (next : List Word→Bool) (ws : List Word) :
    guarded k next ws =
      if ws.length>k+2 then false else
        pairs (pairTry k next ws) (ws.map fun a => (a,privateMask ws a)) := rfl

theorem cover_cons (w : Word) (ws : List Word) : cover (w::ws)=sep w ||| cover ws := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [cover,foldBits,Nat.testBit_or]

theorem drop_len (ws : List Word) (d : Word) (nd : ws.Nodup) (hd : d∈ws) :
    (ws.filter (fun w => w != d)).length+1=ws.length := by
  induction ws with
  | nil => simp at hd
  | cons x xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    by_cases e : x=d
    · subst x
      have self : xs.filter (fun w => w != d)=xs := List.filter_eq_self.mpr (by
        intro v hv
        have neq : v≠d := fun eq => fresh (eq ▸ hv)
        simp [neq])
      simp [self]
    · have hit := (List.mem_cons.mp hd).resolve_left (Ne.symm e)
      have n := ih rest hit
      simp [e,n]

theorem rest_len (ws : List Word) (a b : Word) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b) :
    (restOf ws a b).length+2=ws.length := by
  let after := ws.filter (fun w => w != a)
  have inside : b∈after := by simp [after,hb,ab.symm]
  have n1 := drop_len ws a nd ha
  have n2 := drop_len after b (nd.filter _) inside
  have order : (after.filter (fun w => w != b))=restOf ws a b := by
    simp [after,restOf,List.filter_filter,Bool.and_comm]
  rw [order] at n2
  dsimp [after] at n2
  omega

theorem tryField_hit {k : Nat} {ws : List Word} {a b : Word} (op : Kind) (ka kb : Bool)
    (next : List Word→Bool) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (non : wordGate op a b≠(0,0)) (fresh : wordGate op a b∉ws)
    (wide : (extension ws a b op ka kb).length≤k+1) (old : cover ws=all)
    (new : cover (extension ws a b op ka kb)=all) (pass : next (extension ws a b op ka kb)=true) :
    tryField k next ws (a,privateMask ws a) (b,privateMask ws b) op=true := by
  have remaining := rest_len ws a b nd ha hb ab
  have same := new.trans old.symm
  cases ka <;> cases kb
  · have l := kept_mask_left op ha hb ab false same
    have r := kept_mask_right op ha hb ab false same
    have cc : cover (restOf ws a b) ||| sep (wordGate op a b)=all := by
      simpa [extension,keepList,cover_cons,Nat.or_comm] using new
    simp [extension,keepList] at pass
    simp [tryField,l,r,non,fresh,cc,pass]
  · have l := kept_mask_left op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,l,width,non,fresh,pass]
  · have r := kept_mask_right op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,r,width,non,fresh,pass]
  · have width : ws.length≤k := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,width,non,fresh,pass]

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem project_inj {a b : CoThetaBits.Wire} (h : project a=project b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

@[simp] theorem project_eq {a b : CoThetaBits.Wire} : project a=project b ↔ a=b :=
  ⟨project_inj,congrArg project⟩

private theorem mask_sub {n} (a b : BitVec n) :
    (a &&& ~~~b)=a ^^^ (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem mask_rev {n} (a b : BitVec n) :
    (~~~a &&& b)=b ^^^ (b &&& a) := by rw [BitVec.and_comm,mask_sub]

theorem project_gate (op : Kind) (a b : CoThetaBits.Wire) :
    project (CoThetaBits.gate op a b)=wordGate op (project a) (project b) := by
  cases op <;> simp only [project,CoThetaBits.gate,wordGate,meet,join,skip,mask_sub,mask_rev,
    BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_xor]

theorem project_cover (ws : List CoThetaBits.Wire) :
    cover (ws.map project)=(CoThetaBits.coverage ws).toNat := by
  induction ws with
  | nil => change 0=(0:CoThetaBits.Bits).toNat; simp
  | cons w ws ih => simp [cover_cons,project,sep,CoThetaBits.coverage,CoThetaBits.sep,ih]

theorem project_trim (xs : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) :
    (CoThetaBits.trim a b xs).map project=restOf (xs.map project) (project a) (project b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=a <;> by_cases h : x=b <;>
      simp [CoThetaBits.trim,restOf,e,h,project_eq] at * <;> exact ih

theorem project_edit (ws : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) (op : Kind)
    (U : (CoThetaBits.Row→Bool)→Prop) :
    (CoThetaBits.gate op a b::(CoThetaBits.kept a b U++CoThetaBits.trim a b ws)).map project=
      extension (ws.map project) (project a) (project b) op
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den a))))
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den b)))) := by
  classical
  by_cases p : U (CoThetaBits.den a) <;> by_cases q : U (CoThetaBits.den b) <;>
    simp [CoThetaBits.kept,extension,keepList,p,q,project_gate,project_trim]

theorem pair_hit (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind)
    (h : tryField k next ws a b op=true) : pairTry k next ws a b=true := by
  cases op <;> simp [pairTry,h]

theorem pairs_hit {α} (test : α→α→Bool) {a b : α} {ws : List α}
    (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (go : test a b=true) (back : test b a=true) :
    pairs test ws=true := by
  classical
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    rw [pairs,Bool.or_eq_true]
    by_cases eq : a=w
    · subst w
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left ne.symm,go⟩)
    · by_cases e : b=w
      · subst w
        exact Or.inl (List.any_eq_true.mpr ⟨a,(List.mem_cons.mp ha).resolve_left ne,back⟩)
      · exact Or.inr (ih ((List.mem_cons.mp ha).resolve_left eq) ((List.mem_cons.mp hb).resolve_left e))

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

private theorem project_nodup {xs : List Wire} (h : xs.Nodup) : (xs.map project).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨no,rest⟩ := List.nodup_cons.mp h
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih rest⟩
    intro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact no (project_inj eq ▸ hb)

private theorem seen_iff {S ws} (rep : Rep ws S) (a : Wire) : a∈ws ↔ S (den a) := by
  constructor
  · exact fun ha => (rep _).2 ⟨a,ha,rfl⟩
  · intro h
    obtain ⟨b,hb,eq⟩ := (rep _).1 h
    exact CoThetaBits.den_injective eq ▸ hb

private theorem direction_hit {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      guardedSearch k (zs.map project)=true) :
    pairTry k (guardedSearch k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem guarded_complete {m S} (run : Live (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → guardedSearch fuel (ws.map project)=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    cases fuel <;> simp [guardedSearch,target,hit]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → guardedSearch k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := direction_hit kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (guardedSearch k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply direction_hit (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (guardedSearch k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [guardedSearch,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench
namespace CoThetaSix
open CoThetaBits
open CoNatBench
def cycle : List CoThetaBits.Wire := [(0x401f80fff40701fff,0x400f006ba486086a6),
(0x81e3f3070807ffe00,0x80a1a10608232d414),
(0x3067c0c180ff801fff,0x3027004100a3001958),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07800fe00ffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc05000ac005c4d0020),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000ffff00000000,0x590000f94410060040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa675a4000820080180)]
theorem cycle_small : CoNatBench.guardedSearch 7 (cycle.map CoNatBench.project)=false := by decide +kernel
def cyclePrivate : List Nat := [3, 16, 1, 14, 33, 49]
def pendant : List CoThetaBits.Wire := [(0x118fc1cffbf0601ff,0x108780c5d1e420896),
(0x2071fe33847fffe00,0x2020d213003924c04),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc19e003c07807ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc118002806005b168),
(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01e007c007ff80000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05c00580074602030),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fff80000000,0x56400073a20080c040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa99dd2000400010180)]
theorem pendant_small : CoNatBench.guardedSearch 7 (pendant.map CoNatBench.project)=false := by decide +kernel
def pendantPrivate : List Nat := [3, 12, 1, 20, 32, 48]
end CoThetaSix
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)

def essentialBasis (roots : List Wire) : Prop :=
  ∀ w∈roots, ∃ i : Fin CoThetaBits.Width, ∀ v∈roots,
    den v (true,i)≠den v (false,i) → v=w

theorem generic_rep {m S} {roots : List Wire} (live : Live (den CoThetaBits.target) m S)
    (onlyRaw : ∀ f, S f → f=absentBit ∨ ∃ w∈roots, den w=f)
    (required : essentialBasis roots) : Rep roots S := by
  have ng : den CoThetaBits.target≠absentBit := by
    intro e
    have no := congrFun e (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  intro f
  constructor
  · intro hf
    rcases onlyRaw f hf with z|h
    · exact (live.excludes_zero ng (z ▸ hf)).elim
    · exact h
  · rintro ⟨w,hw,eq⟩
    obtain ⟨i,key⟩ := required w hw
    have d : den CoThetaBits.target (true,i)≠den CoThetaBits.target (false,i) := by simp [CoThetaBits.den_target]
    obtain ⟨v,hv,diff⟩ := live.separates (true,i) (false,i) d
    rcases onlyRaw v hv with z|⟨u,hu,e⟩
    · subst v
      exact (diff rfl).elim
    · subst v
      obtain rfl := key u hu diff
      exact eq ▸ hv

theorem table_bound {roots : List Wire} (required : essentialBasis roots)
    (nd : roots.Nodup) {n ws} (run : Free (absentBit::roots.map den) n ws)
    (goal : den CoThetaBits.target∈ws) {cap : Nat} (cert : guardedSearch cap (roots.map project)=false) : cap<n := by
  obtain ⟨k,S,le,live,sub⟩ := rewind run List.mem_cons_self
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  apply Classical.byContradiction
  intro bad
  apply Bool.false_ne_true
  rw [←cert]
  apply guarded_complete live cap (by omega) roots nd
  apply generic_rep live _ required
  intro f h
  rcases List.mem_cons.mp (sub f h) with z|raw
  · exact Or.inl z
  · exact Or.inr (List.mem_map.mp raw)

end CoNatBench

namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den)

def basisAt (ws : List Wire) (ids : List Nat) : Bool :=
  (List.range ws.length).all fun a =>
    let i := (ids.getD a 0) % CoThetaBits.Width
    ws.all fun v =>
      let want := ws.getD a CoThetaBits.zero
      (den v (true,⟨i,Nat.mod_lt _ (by decide)⟩) == den v (false,⟨i,Nat.mod_lt _ (by decide)⟩)) || v==want

theorem basisAt_sound (ws : List Wire) (ids : List Nat) (cert : basisAt ws ids=true) :
    CoNatBench.essentialBasis ws := by
  intro w hw
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hw
  let i := (ids.getD k 0) % CoThetaBits.Width
  refine ⟨⟨i,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro v hv ne
  have each := List.all_eq_true.mp cert k (List.mem_range.mpr hk)
  have hit := List.all_eq_true.mp each v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at hit
  have vwant := hit.resolve_left ne
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,eq] using vwant

theorem cycle_basis : CoNatBench.essentialBasis cycle := basisAt_sound cycle cyclePrivate (by decide +kernel)
theorem pendant_basis : CoNatBench.essentialBasis pendant := basisAt_sound pendant pendantPrivate (by decide +kernel)
theorem cycle_nd : cycle.Nodup := by decide +kernel
theorem pendant_nd : pendant.Nodup := by decide +kernel

end CoThetaSix
namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)

def rootsFor (gone : Fin 7) := if gone=2 then cycle else pendant

def indexAt (gone vertex : Fin 7) : Option Nat :=
  match gone.val,vertex.val with
  | 2,0 => some 0
  | 2,1 => some 1
  | 2,3 => some 2
  | 2,4 => some 3
  | 2,5 => some 4
  | 2,6 => some 5
  | 3,0 => some 0
  | 3,1 => some 1
  | 3,2 => some 2
  | 3,4 => some 3
  | 3,5 => some 4
  | 3,6 => some 5
  | 4,1 => some 0
  | 4,0 => some 1
  | 4,2 => some 2
  | 4,3 => some 3
  | 4,6 => some 4
  | 4,5 => some 5
  | 5,0 => some 0
  | 5,1 => some 1
  | 5,2 => some 2
  | 5,6 => some 3
  | 5,3 => some 4
  | 5,4 => some 5
  | 6,1 => some 0
  | 6,0 => some 1
  | 6,2 => some 2
  | 6,5 => some 3
  | 6,4 => some 4
  | 6,3 => some 5
  | _,_ => none

def minorCol (gone vertex : Fin 7) : Wire :=
  match indexAt gone vertex with
  | none => CoThetaBits.zero
  | some n => (rootsFor gone).getD n CoThetaBits.zero

def minorLift (g : Fin 7) (r : Row) : SmallInput := pack (fun j => den (minorCol g j) r)
def minorGraph (g : Fin 7) : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (minorCol g 0) (minorCol g 2)) (gate .conj (minorCol g 1) (minorCol g 2)))
    (gate .conj (minorCol g 0) (minorCol g 3))) (gate .conj (minorCol g 3) (minorCol g 4)))
    (gate .conj (minorCol g 1) (minorCol g 4))) (gate .conj (minorCol g 0) (minorCol g 5)))
    (gate .conj (minorCol g 5) (minorCol g 6))) (gate .conj (minorCol g 1) (minorCol g 6))

theorem minor_table : ∀ g : Fin 7, 2≤g.val → minorGraph g=CoThetaBits.target ∧
    minorCol g g=CoThetaBits.zero := by decide +kernel

theorem minor_input (g j : Fin 7) :
    restrict (minorLift g) (raw7 j)=den (minorCol g j) :=
  funext (fun r => unpack (fun v => den (minorCol g v) r) j)

theorem minor_goal {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) ans7=den CoThetaBits.target := by
  have graph := congrArg den (minor_table g small).1
  funext r
  change ans7 (minorLift g r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (minorLift g r))=(fun j => den (minorCol g j) r) :=
    funext (fun j => congrFun (minor_input g j) r)
  rw [values]
  have equality := congrFun graph r
  simp only [minorGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem minor_off {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) (raw7 g)=absentBit :=
  (minor_input g g).trans ((congrArg den (minor_table g small).2).trans CoThetaBits.den_zero)

theorem minor_known (g : Fin 7) : ∀ w∈vertices7,
    restrict (minorLift g) w∈absentBit::(rootsFor g).map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [minor_input]
    cases h : indexAt g j with
    | none => simp [minorCol,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : (rootsFor g)[n]? with
      | none => simp [minorCol,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [minorCol,h,List.getD_eq_getElem?_getD,hn,inList]

theorem minor_lower {g : Fin 7} (small : 2≤g.val) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : 8≤remaining (minorLift g) gs := by
  let roots := rootsFor g
  obtain ⟨ws,run,all⟩ := restrict_trace (minorLift g) gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self (minor_known g)
  have h := all ans7 ok.2
  rw [minor_goal small] at h
  have yes : 7<0+remaining (minorLift g) gs := by
    by_cases e : g=2
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using cycle_basis)
        (by simpa [roots,rootsFor,e] using cycle_nd) run h (by simpa [roots,rootsFor,e] using cycle_small)
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using pendant_basis)
        (by simpa [roots,rootsFor,e] using pendant_nd) run h (by simpa [roots,rootsFor,e] using pendant_small)
  omega

end CoThetaSix
namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

noncomputable def readerSet {ρ : Type} (gs : List (TraceGate ρ)) (p : ρ → Bool) :
    Finset (TraceGate ρ) := by classical exact gs.toFinset.filter (fun g => reads g p)

theorem mem_readerSet {ρ : Type} {gs : List (TraceGate ρ)} {p : ρ → Bool}
    {g : TraceGate ρ} : g ∈ readerSet gs p ↔ g ∈ gs ∧ reads g p := by
  classical
  simp [readerSet]

 

theorem three_readers_separate_head {α : Type} [DecidableEq α] (P Q : Finset α)
    (twoP : 2 ≤ P.card) (someQ : Q.Nonempty) (head : ∃ g ∈ P, g ∉ Q)
    (shared : ∀ g ∈ P, g ∈ Q → 2 ≤ Q.card) : 3 ≤ (P ∪ Q).card := by
  classical
  by_cases both : ∃ g ∈ P, g ∈ Q
  · obtain ⟨g,hg,hq⟩ := both
    obtain ⟨h,hp,hn⟩ := head
    have sub : insert h Q ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_left _ hp
      · exact Finset.mem_union_right _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hn] at hc
    have low := shared g hg hq
    omega
  · obtain ⟨q,hq⟩ := someQ
    have out : q ∉ P := fun hp => both ⟨q,hp,hq⟩
    have sub : insert q P ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ hq
      · exact Finset.mem_union_left _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem out] at hc
    omega

 
inductive UsePath {ρ : Type} (gs : List (TraceGate ρ)) :
    (ρ → Bool) → (ρ → Bool) → Prop
  | stop {w} : UsePath gs w w
  | through {w out} (g : TraceGate ρ) (mem : g ∈ gs) (input : reads g w)
      (rest : UsePath gs g.value out) : UsePath gs w out

private theorem two_reads_zero {ρ σ : Type} (lift : σ → ρ)
    {g : TraceGate ρ} {w p : ρ → Bool} (ne : w ≠ p) (hw : reads g w) (hp : reads g p)
    (zw : restrict lift w = absentBit) (zp : restrict lift p = absentBit) :
    restrict lift g.value = absentBit := by
  apply two_zero_propagate
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h).trans zw
    · exact (congrArg (restrict lift) h').trans zp
    · exact (ne (h.symm.trans h')).elim
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h').trans zp
    · exact (congrArg (restrict lift) h).trans zw
    · exact (ne (h.symm.trans h')).elim

 



theorem extra_loss_on_path {ρ σ : Type} (lift : σ → ρ) {gs : List (TraceGate ρ)}
    {p q z out : ρ → Bool} (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (aliasFree : ∀ g ∈ gs, g.value ≠ p ∧ g.value ≠ q)
    (path : UsePath gs z out) (zz : restrict lift z = absentBit)
    (distinct : z ≠ p ∧ z ≠ q) (ends : restrict lift out ≠ absentBit) :
    ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g := by
  induction path with
  | stop => exact (ends zz).elim
  | @through w out g hg hw more ih =>
    by_cases hp : reads g p
    · exact ih (two_reads_zero lift distinct.1 hw hp zz zp) (aliasFree g hg) ends
    by_cases hq : reads g q
    · exact ih (two_reads_zero lift distinct.2 hw hq zz zq) (aliasFree g hg) ends
    exact ⟨g,hg,hp,hq,reading_zero_disappears lift zz hw⟩

private noncomputable def lostList {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    List (TraceGate ρ) := by classical exact gs.filter (fun g => decide (disappears lift g))

private theorem lost_length {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    (lostList lift gs).length = saved lift gs := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [lostList,saved,h,lostList] at ih ⊢ <;> omega

theorem four_saved_raw_head {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ))
    (p q : ρ → Bool) (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (three : 3 ≤ (readerSet gs p ∪ readerSet gs q).card)
    (extra : ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g) :
    4 ≤ saved lift gs := by
  classical
  obtain ⟨g,hg,hp,hq,hd⟩ := extra
  let A := readerSet gs p ∪ readerSet gs q
  have hout : g ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact hp (mem_readerSet.mp h).2
    · exact hq (mem_readerSet.mp h).2
  have sub : insert g A ⊆ (lostList lift gs).toFinset := by
    intro v hv
    have hv' : v∈gs ∧ disappears lift v := by
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨hg,hd⟩
      · rcases Finset.mem_union.mp hv with h|h
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zp hr⟩
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zq hr⟩
    simpa [lostList] using hv'
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  rw [Finset.card_insert_of_notMem hout,lost_length] at bound
  change 3 ≤ A.card at three
  omega

end CoThetaFreeCore
namespace CoThetaFreeCore

theorem UsePath.trans {ρ : Type} {chain : List (TraceGate ρ)} {a b c : ρ → Bool}
    (first : UsePath chain a b) (last : UsePath chain b c) : UsePath chain a c := by
  induction first with
  | stop => exact last
  | through g hg hr _ ih => exact .through g hg hr (ih last)

 

theorem omit_path_scan {ρ : Type} (chain : List (TraceGate ρ)) (z : ρ → Bool)
    (gs : List (TraceGate ρ)) (sub : ∀ g∈gs, g∈chain)
    {raw start pool : List (ρ → Bool)} {b : Nat}
    (reg : registered start gs) (pre : Free raw b pool)
    (known : ∀ w∈start, ¬UsePath chain z w → w∈pool) :
    ∃ j ys, j ≤ b+gs.length ∧ Free raw j ys ∧
      ∀ w∈traceWires start gs, ¬UsePath chain z w → w∈ys := by
  induction gs generalizing start pool b with
  | nil => exact ⟨b,pool,by simp,pre,known⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,rest⟩ := reg
    have hg := sub g List.mem_cons_self
    have tail (v) (hv : v∈gs) := sub v (List.mem_cons_of_mem _ hv)
    by_cases path : UsePath chain z g.value
    · have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact (hn path).elim
        · exact known _ hw hn
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest pre carry
      exact ⟨j,ys,by simp; omega,run,avail⟩
    · have pl : ¬UsePath chain z g.left := fun p =>
        path (p.trans (.through g hg (Or.inl rfl) .stop))
      have pr : ¬UsePath chain z g.right := fun p =>
        path (p.trans (.through g hg (Or.inr rfl) .stop))
      have next : Free raw (b+1) (g.value::pool) :=
        .binary pre g.kind (known _ hl pl) (known _ hr pr)
      have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈g.value::pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (known _ hw hn)
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest next carry
      exact ⟨j,ys,by simp; omega,run,avail⟩

theorem omit_dead_head {ρ : Type} (raw : List (ρ → Bool))
    (gs : List (TraceGate ρ)) (z target : ρ → Bool)
    (reg : registered (z::raw) gs) (out : target∈traceWires (z::raw) gs)
    (dead : ¬UsePath gs z target) :
    ∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ target∈ys := by
  have known (w) (hw : w∈z::raw) (hn : ¬UsePath gs z w) : w∈raw := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact (hn .stop).elim
    · exact hw
  obtain ⟨j,ys,hj,run,avail⟩ := omit_path_scan gs z gs (fun _ h => h) reg (Free.start (raw:=raw)) known
  exact ⟨j,ys,by simpa using hj,run,avail _ out dead⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

private theorem masked_setting {ρ : Type} (g : TraceGate ρ) (p : ρ → Bool) (hp : reads g p) :
    ∃ b : Bool, ∀ r s, p r=b → p s=b → g.value r = g.value s := by
  obtain ⟨k,l,r⟩ := g
  rcases hp with h|h
  · change l=p at h
    subst l
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k b a = applyKind k b c := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩
  · change r=p at h
    subst r
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k a b = applyKind k c b := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩

 

theorem nonedge_head_dichotomy {ρ σ : Type} (lift : σ → ρ)
    (raw : List (ρ → Bool)) (head : TraceGate ρ) (gs : List (TraceGate ρ))
    (p q out : ρ → Bool)
    (reg : registered raw (head::gs)) (solves : out∈traceWires raw (head::gs))
    (hrp : reads head p) (hrq : ¬reads head q)
    (outp : out≠p) (outq : out≠q)
    (pTest : ∃ r s, agreeOutside (·=p) r s raw ∧ out r≠out s ∧ head.value r=head.value s)
    (qTest : ∀ b : Bool, ∃ r s, agreeOutside (·=q) r s raw ∧ out r≠out s ∧ p r=b ∧ p s=b)
    (zp : restrict lift p=absentBit) (zq : restrict lift q=absentBit)
    (zh : restrict lift head.value=absentBit) (endNZ : restrict lift out≠absentBit)
    (headNew : head.value≠p ∧ head.value≠q)
    (fresh : ∀ g∈gs, g.value≠p ∧ g.value≠q) :
    (∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ out∈ys) ∨ 4 ≤ saved lift (head::gs) := by
  classical
  by_cases alive : UsePath gs head.value out
  case neg =>
    exact Or.inl (omit_dead_head raw gs head.value out reg.2.2 solves alive)
  case pos =>
    right
    apply four_saved_raw_head lift (head::gs) p q zp zq
    · apply three_readers_separate_head
      · obtain ⟨r,s,hs,hd,hm⟩ := pTest
        obtain ⟨g,hg,hp,ne⟩ := second_reader p r s head reg hs solves outp hd hm
        apply Finset.one_lt_card.mpr
        exact ⟨g,mem_readerSet.mpr ⟨hg,hp⟩,head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,ne⟩
      · obtain ⟨r,s,hs,hd,_,_⟩ := qTest false
        obtain ⟨g,hg,read,_⟩ := reader_witness (·=q) r s reg hs solves outq hd
        exact ⟨g,mem_readerSet.mpr ⟨hg,read⟩⟩
      · exact ⟨head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,fun h => hrq (mem_readerSet.mp h).2⟩
      · intro g hgP hgQ
        obtain ⟨b,hm⟩ := masked_setting g p (mem_readerSet.mp hgP).2
        obtain ⟨r,s,hs,hd,hpR,hpS⟩ := qTest b
        obtain ⟨other,hOther,readsQ,ne⟩ := second_reader q r s g reg hs solves outq hd (hm r s hpR hpS)
        apply Finset.one_lt_card.mpr
        exact ⟨other,mem_readerSet.mpr ⟨hOther,readsQ⟩,g,hgQ,ne⟩
    · obtain ⟨g,hg,hp,hq,hd⟩ := extra_loss_on_path lift zp zq fresh alive zh headNew endNZ
      exact ⟨g,List.mem_cons_of_mem _ hg,hp,hq,hd⟩

end CoThetaFreeCore
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off minor_goal minor_lower)

def smallRow (n : Nat) : SmallInput := ⟨n % 128,Nat.mod_lt _ (by decide)⟩
def sensSeeds : List Nat :=
  [0, 0, 4, 10, 8, 4, 4, 8, 4, 20, 4, 32, 4, 68, 4, 17, 0, 0, 16, 4, 4, 12, 4, 16, 4, 36, 4, 64, 2, 1, 1, 2, 0, 0, 1, 10, 1, 17, 1, 34, 1, 65, 16, 1, 1, 3, 1, 20, 0, 0, 1, 16, 1, 48, 1, 65, 2, 3, 8, 2, 2, 12, 2, 8, 0, 0, 2, 34, 2, 72, 64, 1, 1, 3, 1, 68, 1, 72, 1, 17, 0, 0, 1, 64, 2, 3, 32, 2, 2, 36, 2, 10, 2, 48, 2, 32, 0, 0]

def loRow (x y : Fin 7) (b : Bool) := smallRow (sensSeeds.getD (2*(7*x.val+y.val)+b.toNat) 0)
def hiRow (x y : Fin 7) (b : Bool) := smallRow ((loRow x y b).val ||| (1 <<< x.val))
theorem seven_sensitivity : ∀ (x y : Fin 7), x≠y → ∀ b : Bool,
    raw7 x (loRow x y b)=false ∧ raw7 x (hiRow x y b)=true ∧
    raw7 y (loRow x y b)=b ∧ raw7 y (hiRow x y b)=b ∧
    ans7 (loRow x y b)≠ans7 (hiRow x y b) ∧
    ∀ z : Fin 7, z≠x → raw7 z (loRow x y b)=raw7 z (hiRow x y b) := by decide +kernel

theorem seven_diff : ∀ (x y : Fin 7), x≠y → ∃ r : SmallInput, raw7 x r≠raw7 y r := by
  have table : ∀ p q : Fin 7, p≠q → raw7 p (smallRow (1 <<< p.val))≠raw7 q (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p q pq => ⟨_,table p q pq⟩
theorem seven_not_raw : ∀ x : Fin 7, ∃ r : SmallInput, ans7 r≠raw7 x r := by
  have table : ∀ p : Fin 7, ans7 (smallRow (1 <<< p.val))≠raw7 p (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p => ⟨_,table p⟩

theorem raw_mem (x : Fin 7) : raw7 x∈vertices7 := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x,rfl⟩)

theorem read_twice (x y : Fin 7) (xy : x≠y) (g : TraceGate SmallInput)
    (gx : reads g (raw7 x)) (gy : reads g (raw7 y)) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : ∃ t∈gs, reads t (raw7 x) ∧ t≠g := by
  obtain ⟨r,ne⟩ := seven_diff x y xy
  have diff : raw7 x≠raw7 y := fun h => ne (congrFun h r)
  obtain ⟨sw,code⟩ := joint_reader_code _ _ diff g gx gy
  obtain ⟨b,mask⟩ := CoThetaNine.masks_some_value g.kind sw
  obtain ⟨lx,hx,ly,hy,out,fixed⟩ := seven_sensitivity x y xy b
  obtain ⟨r,notSame⟩ := seven_not_raw x
  apply second_reader (raw7 x) (loRow x y b) (hiRow x y b) g ok.1 _ ok.2
    (fun eq => notSame (congrFun eq r)) out
  · simpa only [code,lx,hx,ly,hy] using mask false true
  · intro w hw no
    rcases List.mem_cons.mp hw with e|h
    · subst w
      rfl
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp h
      subst w
      exact fixed i (fun e => no (congrArg raw7 e))

theorem three_losses {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) {a b c : TraceGate ρ}
    (ha : a∈gs) (hb : b∈gs) (hc : c∈gs) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (da : disappears lift a) (db : disappears lift b) (dc : disappears lift c) :
    3≤saved lift gs := by
  classical
  have nd : [a,b,c].Nodup := by simp [ab,ac,bc]
  rw [saved_eq_length]
  apply length_of_cover [a,b,c] _ nd
  intro w h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e <;> subst w <;> simp [vanishing,ha,hb,hc,da,db,dc]

theorem absorbing_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (budget : (g::gs).length≤10) {x y : Fin 7} (xy : x≠y)
    (rx : reads g (raw7 x)) (ry : reads g (raw7 y)) (nonhub : 2≤x.val)
    (zero : restrict (minorLift x) g.value=absentBit) :
    ∃ n ws, n≤gs.length ∧ Free vertices7 n ws ∧ ans7∈ws := by
  classical
  by_cases path : UsePath gs g.value ans7
  · exfalso
    have off := minor_off nonhub
    have fin : restrict (minorLift x) ans7≠absentBit := by
      rw [minor_goal nonhub]
      intro e
      have no := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at no
    have distinct {t : TraceGate SmallInput} (ht : t∈g::gs) : t.value≠raw7 x :=
      fun e => fresh_outputs fresh _ ht (e ▸ raw_mem x)
    have headNe := distinct (List.mem_cons_self (a:=g) (l:=gs))
    obtain ⟨b,hb,rb,bg⟩ := read_twice x y xy g rx ry ok
    obtain ⟨c,hc,nr,_,gone⟩ := extra_loss_on_path (minorLift x) off off
      (fun t ht => ⟨distinct (List.mem_cons_of_mem _ ht),distinct (List.mem_cons_of_mem _ ht)⟩)
      path zero ⟨headNe,headNe⟩ fin
    have gain := three_losses (minorLift x) (g::gs) List.mem_cons_self hb
      (List.mem_cons_of_mem _ hc) (Ne.symm bg) (fun e => nr (e ▸ rx)) (fun e => nr (e ▸ rb))
      (reading_zero_disappears _ off rx) (reading_zero_disappears _ off rb) gone
    have lo := minor_lower nonhub ok
    have tot := accounted (minorLift x) (g::gs)
    omega
  · exact omit_dead_head vertices7 gs g.value ans7 ok.1.2.2 ok.2 path

end CoThetaSeven
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off)
def opIndex : Kind→Nat
  | .conj => 0 | .disj => 1 | .leftOnly => 2 | .rightOnly => 3
def opAt (n : Nat) : Kind := match n with
  | 0 => .conj | 1 => .disj | 2 => .leftOnly | _ => .rightOnly
def allPerms : List (List (Fin 7)) := [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 5, 6, 3, 4], [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 6, 5, 4, 3]]
def casesA : List (Fin 7) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3]
def casesB : List (Fin 7) := [1, 1, 1, 2, 2, 3, 3, 4, 4, 3, 4, 5, 6]
def casesOp : List Nat := [0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1]
def tags : List Nat := [0, 0, 0, 0, 2, 6, 10, 12, 1, 14, 18, 1, 1, 22, 26, 1, 1, 30, 34, 1, 1, 23, 27, 1, 1, 31, 35, 1, 2, 6, 12, 10, 0, 0, 0, 0, 1, 16, 20, 1, 1, 32, 36, 1, 1, 24, 28, 1, 1, 33, 37, 1, 1, 25, 29, 1, 0, 14, 0, 18, 0, 16, 0, 20, 0, 0, 0, 0, 0, 38, 0, 1, 0, 40, 0, 1, 0, 39, 0, 1, 0, 41, 0, 1, 0, 22, 0, 26, 0, 32, 0, 36, 0, 38, 0, 1, 0, 0, 0, 0, 0, 42, 0, 1, 0, 46, 0, 1, 0, 50, 0, 1, 0, 30, 0, 34, 0, 24, 0, 28, 0, 40, 0, 1, 0, 42, 0, 1, 0, 0, 0, 0, 0, 51, 0, 1, 0, 48, 0, 1, 0, 23, 0, 27, 0, 33, 0, 37, 0, 39, 0, 1, 0, 46, 0, 1, 0, 51, 0, 1, 0, 0, 0, 0, 0, 43, 0, 1, 0, 31, 0, 35, 0, 25, 0, 29, 0, 41, 0, 1, 0, 50, 0, 1, 0, 48, 0, 1, 0, 43, 0, 1, 0, 0, 0, 0]
def numbered (i : Fin 13) : TraceGate SmallInput :=
  ⟨opAt (casesOp.getD i.val 0),raw7 (casesA.getD i.val 0),raw7 (casesB.getD i.val 0)⟩
def position (s : Fin 4) (j : Fin 7) := (allPerms.getD s.val []).getD j.val 0
def rowPerm (s : Fin 4) (r : SmallInput) := pack (fun j => raw7 (position s j) r)
def tag (x y : Fin 7) (op : Kind) := tags.getD (4*(7*x.val+y.val)+opIndex op) 0
def picked (n : Nat) : Fin 13 := ⟨((n-2)/4) % 13,Nat.mod_lt _ (by decide)⟩
def rotation (n : Nat) : Fin 4 := ⟨(n-2) % 4,Nat.mod_lt _ (by decide)⟩

theorem perm_graph : ∀ (s : Fin 4) (r : SmallInput), ans7 (rowPerm s r)=ans7 r := by decide +kernel

theorem raw_permute (s : Fin 4) (j : Fin 7) :
    restrict (rowPerm s) (raw7 j)=raw7 (position s j) :=
  funext (fun r => unpack (fun k => raw7 (position s k) r) j)

theorem dispatch_rules (op : Kind) : ∀ x y : Fin 7, x≠y →
    let n := tag x y op
    if n=0 then 2≤x.val ∧ ∀ b : Bool, applyKind op false b=false else
    if n=1 then 2≤y.val ∧ ∀ a : Bool, applyKind op a false=false else
    ∀r : SmallInput, applyKind op (raw7 x (rowPerm (rotation n) r)) (raw7 y (rowPerm (rotation n) r)) =
      (numbered (picked n)).value r := by
  cases op <;> decide +kernel

def Selected : Prop := (∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws) ∨
  ∃ i : Fin 13, ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem dispatch_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (size : (g::gs).length≤10) : Selected := by
  classical
  obtain ⟨nL,nR,separate⟩ := fresh_ports g ok.1.1 ok.1.2.1 List.mem_cons_self fresh.1
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.1).resolve_left nL)
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.2.1).resolve_left nR)
  have xy : x≠y := fun e => separate (ex.symm.trans ((congrArg raw7 e).trans ey))
  have rx : reads g (raw7 x) := Or.inl ex.symm
  have ry : reads g (raw7 y) := Or.inr ey.symm
  let t := tag x y g.kind
  have rule := dispatch_rules g.kind x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  have n : gs.length≤9 := by simp only [List.length_cons] at size; omega
  by_cases a : t=0
  · rw [if_pos a] at rule
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind g.kind (g.left (minorLift x r)) (g.right (minorLift x r))=false
      rw [←ex,←ey]
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size xy rx ry rule.1 drop
    exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind g.kind (g.left (minorLift y r)) (g.right (minorLift y r))=false
        rw [←ex,←ey]
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size (Ne.symm xy) ry rx rule.1 drop
      exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
    · rw [if_neg b] at rule
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := by
        funext r
        change applyKind g.kind (g.left (rowPerm s r)) (g.right (rowPerm s r))=_
        rw [←ex,←ey]
        exact rule r
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨ws,run,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact Or.inr ⟨i,_,ws,by omega,run,goal⟩

theorem select_program {n ws} (run : Free vertices7 n ws) (small : n≤10) (hit : ans7∈ws) :
    Selected := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,solves,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  cases clean with
  | nil =>
    have h : ans7∈vertices7 := solves.2
    rcases List.mem_cons.mp h with z|r
    · have test : ans7 (smallRow 5)=true := by decide
      exact Bool.noConfusion (test.symm.trans (congrFun z (smallRow 5)))
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
      obtain ⟨s,d⟩ := seven_not_raw i
      exact (d (congrFun e.symm s)).elim
  | cons g gs => exact dispatch_head solves fresh (by omega)

end CoThetaSeven
namespace CoNatBench

def firstPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]
def secondPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

def rootWords : List Word := CoThetaBits.raw.map project
def nth (ws : List Word) (i : Nat) := ws.getD i (0,0)
def kinds (i : Nat) (x y : Word) : Word :=
  match i with | 0 => meet x y | 1 => join x y | 2 => skip x y | _ => skip y x



def firstWords (index : Nat) : List Word :=
  let pair := firstPairs[index/4]?.getD (0,1)
  let a := nth rootWords pair.1
  let b := nth rootWords pair.2
  let z := kinds (index % 4) a b
  z::a::b::(rootWords.filter (fun w => w != a && w != b))

def prefixCase (i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(guardedSearch 8 next)

def casesBlock (i first count : Nat) : Bool :=
  (List.range count).all (fun d => prefixCase i (first+d))

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack toRows numeric_target)
open CoThetaBits (Row Wire den col Rep)

def numbers : List Nat := [0,1,2,5,6,9,10,13,14,45,61,65,69]
def numberedWord (i : Fin 13) :=
  CoThetaBits.gate (numbered i).kind (col (casesA.getD i.val 0)) (col (casesB.getD i.val 0))

def postPool (i : Fin 13) :=
  let a := col (casesA.getD i.val 0)
  let b := col (casesB.getD i.val 0)
  numberedWord i::a::b::CoThetaBits.trim a b CoThetaBits.raw

theorem post_data : ∀ i : Fin 13,
    (postPool i).Nodup ∧ ((postPool i).map CoNatBench.project)=CoNatBench.firstWords (numbers.getD i.val 0) ∧
    ((postPool i).Perm (numberedWord i::CoThetaBits.raw)) ∧
    ∀ j : Fin 7, CoThetaBits.coverage ((postPool i).filter fun v => v != col j)≠CoThetaBits.full := by
  decide +kernel

theorem proj_raw (j : Fin 7) : restrict toRows (raw7 j)=den (col j) :=
  funext (fun r => unpack (CoThetaBits.sample r) j)

theorem proj_head (i : Fin 13) : restrict toRows (numbered i).value=den (numberedWord i) := by
  rw [numberedWord,CoThetaBits.den_gate]
  funext r
  change applyKind (numbered i).kind (raw7 (casesA.getD i.val 0) (toRows r))
    (raw7 (casesB.getD i.val 0) (toRows r))=_
  change applyKind _ (raw7 _ (pack (CoThetaBits.sample r))) (raw7 _ (pack (CoThetaBits.sample r)))=_
  rw [unpack,unpack]
  rfl

theorem collect_init (i : Fin 13) {f : Row→Bool}
    (hf : f∈((numbered i).value::vertices7).map (restrict toRows)) :
    f=absentBit ∨ ∃ w∈postPool i, den w=f := by
  obtain ⟨v,hv,eq⟩ := List.mem_map.mp hf
  subst f
  have perm := (post_data i).2.2.1
  rcases List.mem_cons.mp hv with h|rest
  · subst v
    exact Or.inr ⟨_,perm.mem_iff.mpr List.mem_cons_self,(proj_head i).symm⟩
  rcases List.mem_cons.mp rest with h|final
  · subst v
    exact Or.inl rfl
  · obtain ⟨j,h⟩ := List.mem_ofFn.mp final
    subst v
    have mem : col j∈CoThetaBits.raw := by
      rw [←CoThetaBits.raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact Or.inr ⟨_,perm.mem_iff.mpr (List.mem_cons_of_mem _ mem),(proj_raw j).symm⟩

theorem classify_pool (i : Fin 13) {k S} (live : Live (den CoThetaBits.target) k S)
    (sub : ∀ f, S f → f=absentBit ∨ ∃w∈postPool i,den w=f) :
    Rep CoThetaBits.raw S ∨ Rep (postPool i) S := by
  classical
  have ng : den CoThetaBits.target≠absentBit := by
    intro bad
    have no := congrFun bad (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  have present (f) (h : S f) : ∃w∈postPool i,den w=f := by
    rcases sub f h with z|p
    · exact (live.excludes_zero ng (z ▸ h)).elim
    · exact p
  have core (j : Fin 7) : S (den (col j)) := by
    apply Classical.byContradiction
    intro missing
    apply (post_data i).2.2.2 j
    apply CoThetaBits.live_coverage _ live
    intro f hf
    obtain ⟨w,hw,eq⟩ := present f hf
    have ne : w≠col j := by
      intro same
      exact missing (same ▸ (eq ▸ hf))
    exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [ne]⟩,eq⟩
  have raw_has {w : Wire} (hw : w∈CoThetaBits.raw) : S (den w) := by
    obtain ⟨j,e⟩ := CoThetaBits.indexed hw
    exact e ▸ core j
  have perm := (post_data i).2.2.1
  by_cases hit : S (den (numberedWord i))
  · right
    intro f
    refine ⟨present f,?_⟩
    rintro ⟨w,hw,eq⟩
    rcases List.mem_cons.mp (perm.mem_iff.mp hw) with z|r
    · subst w
      exact eq ▸ hit
    · exact eq ▸ raw_has r
  · left
    intro f
    constructor
    · intro hf
      obtain ⟨w,m,eq⟩ := present f hf
      rcases List.mem_cons.mp (perm.mem_iff.mp m) with e|r
      · subst w
        exact (hit (eq ▸ hf)).elim
      · exact ⟨w,r,eq⟩
    · rintro ⟨w,hw,eq⟩
      exact eq ▸ raw_has hw

def RawNine : Prop := ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep CoThetaBits.raw S → False
def AfterNine : Prop := ∀ i : Fin 13, ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False

theorem impossible_after (r9 : RawNine) (p9 : AfterNine) (i : Fin 13)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  obtain ⟨k,S,le,live,sub⟩ := rewind (run.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live (by omega) raw
  · exact p9 i live (by omega) extra

theorem seven_bound (r9 : RawNine) (p9 : AfterNine) {n ws} (run : Free vertices7 n ws)
    (out : ans7∈ws) : 11≤n := by
  apply Classical.byContradiction
  intro ne
  rcases select_program run (by omega) out with ⟨h,ys,cost,reduced,goal⟩ | ⟨i,h,ys,cost,reduced,goal⟩
  · let raw0 := (vertices7.map (restrict toRows))
    have zero : absentBit∈raw0 := List.mem_cons_self
    have endw := List.mem_map_of_mem (f:=restrict toRows) goal
    rw [numeric_target] at endw
    obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
      (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
    have rep := CoThetaBits.root_rep live (by
      intro f hf
      obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
      subst f
      rcases List.mem_cons.mp hw with z|l
      · subst w
        exact Or.inl rfl
      · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
        subst w
        exact Or.inr ⟨j,(proj_raw j).symm⟩)
    exact r9 live (by omega) rep
  · exact impossible_after r9 p9 i reduced cost goal

end CoThetaSeven
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def Supported (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ guardedSearch k out=true

private theorem support_from {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, Supported k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact guarded_complete tail k enough out d ro

theorem supported_step {m k S} {ws : List Wire} (run : Live (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      Supported k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact support_from op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply support_from (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaBits (Wire Row Rep den)

def keepIndex (a b : Bool) : Nat := a.toNat+2*b.toNat

theorem pair7_index : ∀ a b : Fin 7, a.val<b.val →
    ∃ q : Fin 21, firstPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem pair8_index : ∀ a b : Fin 8, a.val<b.val →
    ∃ q : Fin 28, secondPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem first_keep (op : Kind) : ∀ a b : Fin 7, a.val<b.val → ∀ ka kb : Bool,
    cover (extension rootWords (nth rootWords a.val) (nth rootWords b.val) op ka kb)=all → ka=true ∧ kb=true := by
  cases op <;> decide +kernel

theorem first_repr (op : Kind) (q : Fin 21) :
    let pair := firstPairs[q.val]?.getD (0,1)
    extension rootWords (nth rootWords pair.1) (nth rootWords pair.2) op true true =
    firstWords (4*q.val+opIndex op) := by
  revert q
  cases op <;> decide +kernel

theorem class_data : ∀ i : Fin 13, (postPool i).length=8 ∧ CoThetaBits.target∉postPool i := by decide +kernel
theorem target_out : CoThetaBits.target∉CoThetaBits.raw := by decide +kernel

theorem root_from_cases (checks : ∀ i : Fin 84, guardedSearch 8 (firstWords i.val)=false) : RawNine := by
  intro m S live cost rep
  obtain ⟨a,b,ab,limit,op,ka,kb,hit⟩ := supported_step live CoThetaBits.raw_nodup rep cost target_out
  change b<7 at limit
  let u : Fin 7 := ⟨a,by omega⟩
  let v : Fin 7 := ⟨b,limit⟩
  obtain ⟨q,eq⟩ := pair7_index u v ab
  obtain ⟨_,_,_,cov,more⟩ := hit
  obtain ⟨k1,k2⟩ := first_keep op u v ab ka kb cov
  subst ka
  subst kb
  have link := first_repr op q
  change firstPairs[q.val]?.getD (0,1)=(a,b) at eq
  rw [eq] at link
  change guardedSearch 8 (extension rootWords (nth rootWords a) (nth rootWords b) op true true)=true at more
  rw [link] at more
  have bound : 4*q.val+opIndex op<84 := by
    have h := q.isLt
    cases op <;> simp [opIndex] <;> omega
  exact Bool.false_ne_true ((checks ⟨_,bound⟩).symm.trans more)

theorem digits (q : Nat) (op : Kind) (ka kb : Bool) :
    let n := 16*q+4*opIndex op+keepIndex ka kb
    n/16=q ∧ (n/4) % 4=opIndex op ∧ n % 4=keepIndex ka kb := by
  cases op <;> cases ka <;> cases kb <;> simp [opIndex,keepIndex] <;> omega

theorem bits_op (op : Kind) (a b : Word) : kinds (opIndex op) a b=wordGate op a b := by cases op <;> rfl

theorem prefix_conflict (label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : Supported 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, prefixCase label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  simp only [prefixCase,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,cov,yes]

theorem after_from_cases (checks : ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true) :
    AfterNine := by
  intro i m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := supported_step live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := prefix_conflict (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks i j))

theorem combine_blocks (tests : ∀ i : Fin 13, ∀ b : Fin 38,
    casesBlock (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true := by
  intro i j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests i b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes

end CoThetaSeven

namespace CoNatBench
def rankSignal (z : Word) : Nat :=
  if z.1<0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 || (z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2<0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008) then (if z.1<0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 || (z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0) then (if z.1<0x7fffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1<0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0) then (if z.1<0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0x50138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x80800800000002800400090010a02000080026001401120010a070200282208260134a11080a28a2181401404a then 6 else 20) else (if z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20)) else (if z.1<0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220) then (if z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0 then 0 else 20) else (if z.1<0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0) then (if z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220 then 0 else 20) else (if z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0 then 0 else 20)))) else (if z.1<0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c) then (if z.1<0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff || (z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20)) else (if z.1<0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff || (z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2<0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0) then (if z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c then 6 else 20) else (if z.1<0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2<0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020) then (if z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2==0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0 then 0 else 20) else (if z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2==0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020 then 0 else 20))))) else (if z.1<0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 || (z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1<0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff || (z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2<0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a) then (if z.1<0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0 then 0 else 20) else (if z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)) else (if z.1<0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 || (z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2==0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a then 6 else 20) else (if z.1<0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff || (z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2<0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30) then (if z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20) else (if z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2==0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30 then 0 else 20)))) else (if z.1<0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff || (z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1<0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2<0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300) then (if z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20) else (if z.1<0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00) then (if z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2==0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300 then 0 else 20) else (if z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00 then 0 else 20))) else (if z.1<0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 || (z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2<0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c) then (if z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20) else (if z.1<0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff || (z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2<0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990) then (if z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2==0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c then 6 else 20) else (if z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2==0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990 then 0 else 20)))))) else (if z.1<0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff || (z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1<0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 || (z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2<0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000) then (if z.1<0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00) then (if z.1<0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2<0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100) then (if z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2==0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100 then 0 else 20)) else (if z.1<0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 || (z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00 then 0 else 20) else (if z.1<0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 || (z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 7 else 20) else (if z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 7 else 20)))) else (if z.1<0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2<0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000) then (if z.1<0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 || (z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2<0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040) then (if z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2==0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000 then 0 else 20) else (if z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2==0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040 then 0 else 20)) else (if z.1<0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400) then (if z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2==0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000 then 0 else 20) else (if z.1<0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff || (z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2<0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442) then (if z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400 then 0 else 20) else (if z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2==0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442 then 11 else 20))))) else (if z.1<0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 || (z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2<0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004) then (if z.1<0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 || (z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 || (z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2<0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220) then (if z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2==0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220 then 0 else 20)) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2<0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300) then (if z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2==0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300 then 0 else 20) else (if z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)))) else (if z.1<0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 || (z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2<0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080) then (if z.1<0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 || (z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2==0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004 then 11 else 20) else (if z.1<0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 || (z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20))) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2==0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080 then 0 else 20) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800) then (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800 then 0 else 20))))))) else (if z.1<0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff || (z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2<0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a) then (if z.1<0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1<0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2<0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400) then (if z.1<0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 || (z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2<0x0) then (if z.1<0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff || (z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2<0x0) then (if z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2==0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008 then 5 else 20) else (if z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2==0x0 then 0 else 20)) else (if z.1<0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 || (z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2<0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040) then (if z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2==0x0 then 0 else 20) else (if z.1<0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 || (z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2==0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040 then 0 else 20) else (if z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2==0x0 then 0 else 20)))) else (if z.1<0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 || (z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2<0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000) then (if z.1<0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 || (z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2<0x0) then (if z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2==0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400 then 0 else 20) else (if z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2==0x0 then 0 else 20)) else (if z.1<0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 || (z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2<0x0) then (if z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2==0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000 then 0 else 20) else (if z.1<0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2<0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000) then (if z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2==0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000 then 0 else 20))))) else (if z.1<0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800) then (if z.1<0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 || (z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2<0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220) then (if z.1<0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff || (z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2<0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e) then (if z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2==0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e then 12 else 20)) else (if z.1<0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 || (z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2<0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080) then (if z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2==0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220 then 0 else 20) else (if z.1<0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2<0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300) then (if z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2==0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080 then 0 else 20) else (if z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2==0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300 then 0 else 20)))) else (if z.1<0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 || (z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2<0x0) then (if z.1<0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff || (z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2<0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa) then (if z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800 then 0 else 20) else (if z.1<0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff || (z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2<0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc) then (if z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2==0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa then 1 else 20) else (if z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2==0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc then 1 else 20))) else (if z.1<0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2<0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200) then (if z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1<0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000) then (if z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2==0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200 then 0 else 20) else (if z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000 then 0 else 20)))))) else (if z.1<0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2<0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a) then (if z.1<0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff || (z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2<0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca) then (if z.1<0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff || (z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2<0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0) then (if z.1<0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 || (z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2<0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c) then (if z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2==0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a then 4 else 20) else (if z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2==0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c then 13 else 20)) else (if z.1<0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2<0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000) then (if z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2==0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0 then 10 else 20) else (if z.1<0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000) then (if z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2==0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000 then 0 else 20) else (if z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000 then 0 else 20)))) else (if z.1<0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff || (z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2<0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0) then (if z.1<0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 || (z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2<0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc) then (if z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2==0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca then 13 else 20) else (if z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2==0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc then 4 else 20)) else (if z.1<0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 || (z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2<0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0) then (if z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2==0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2==0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0 then 2 else 20) else (if z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20))))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2<0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a) then (if z.1<0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff || (z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2<0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0) then (if z.1<0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c) then (if z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2==0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a then 4 else 20) else (if z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c then 13 else 20)) else (if z.1<0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2<0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320) then (if z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2==0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2<0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0) then (if z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2==0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2==0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0 then 3 else 20)))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20) then (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a then 13 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c then 4 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0 then 10 else 20))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20 then 3 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00 then 2 else 20)))))))
def headOK (bound : Nat) : List Word → Bool
  | [] => true
  | x::_ => decide (bound≤rankSignal x)

def permittedSearch (bound : Nat) : Nat → List Word → Bool
  | 0,ws => headOK bound ws && ws.contains target
  | k+1,ws => headOK bound ws && (ws.contains target || guarded k (permittedSearch bound k) ws)

end CoNatBench

namespace CoNatBench
def permitPrefix (bound i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if rankSignal z < bound || z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(permittedSearch bound 8 next)

def permitBlock (bound i first count : Nat) : Bool :=
  (List.range count).all (fun d => permitPrefix bound i (first+d))


end CoNatBench

namespace CoThetaFreeCore

variable {ρ : Type}

theorem free_enlarge {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    (base : List (ρ→Bool)) (inc : ∀ f∈raw, f∈base) :
    ∃ xs, Free base k xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact ⟨_,Free.start,inc⟩
  | @binary n us a b pre op ha hb ih =>
    obtain ⟨ys,prev,sub⟩ := ih
    refine ⟨_,Free.binary prev op (sub a ha) (sub b hb),?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with e|old
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub f old)

theorem free_move {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    {w : ρ→Bool} (atEnd : w∈ws) (notRaw : w∉raw) :
    ∃ m xs, m<k ∧ Free (w::raw) m xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact (notRaw atEnd).elim
  | @binary n us a b pre op ha hb ih =>
    by_cases found : w∈us
    · obtain ⟨m,ys,cap,prev,sub⟩ := ih found
      refine ⟨m+1,_,by omega,Free.binary prev op (sub a ha) (sub b hb),?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sub f old)
    · have eq := (List.mem_cons.mp atEnd).resolve_right found
      obtain ⟨ys,prev,sub⟩ := free_enlarge pre (w::raw) (fun _ h => List.mem_cons_of_mem _ h)
      refine ⟨n,ys,by omega,prev,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact (e.trans eq.symm).symm ▸ free_keeps_raw prev List.mem_cons_self
      · exact sub f old

end CoThetaFreeCore

namespace CoThetaFreeCore
variable {ρ : Type}
inductive Marked (p : (ρ→Bool)→Prop) (goal : ρ→Bool) : Nat→((ρ→Bool)→Prop)→Prop
  | stop (allowed : p goal) : Marked p goal 0 (fun v => v=goal)
  | step {k U a b} (allowed : ∀ w, ins a (ins b U) w → p w)
      (kind : Kind) (ab : a≠b) (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Marked p goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Marked p goal (k+1) (ins a (ins b U))

theorem Marked.live {p : (ρ→Bool)→Prop} {goal k S} (r : Marked p goal k S) : Live goal k S := by
  induction r with
  | stop => exact .stop
  | step _ op ab ha hb fresh _ ih => exact .step op ab ha hb fresh ih

theorem Marked.allowed {p : (ρ→Bool)→Prop} {goal k S} (r : Marked p goal k S) : ∀ w, S w → p w := by
  cases r with
  | stop good => exact fun w h => h.symm ▸ good
  | step allow _ _ _ _ _ _ => exact allow

theorem rewindMarked {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {p : (ρ→Bool)→Prop} (hs : ∀ w∈ws, p w) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Marked p goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Marked p goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Marked p goal (k+1) (ins a (ins b U)) :=
          Marked.step (fun w h => hs w (List.mem_cons_of_mem _ (memAll w h))) kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

def allowedWire (bnd : Nat) (f : Row→Bool) : Prop := ∀ v : Wire, den v=f → bnd≤rankSignal (project v)

theorem head_allowed {bnd ws S} (rep : Rep ws S) (h : ∀ f, S f → allowedWire bnd f) :
    headOK bnd (ws.map project)=true := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    change decide (bnd≤rankSignal (project w))=true
    exact decide_eq_true_eq.mpr (h (den w) ((rep _).2 ⟨w,List.mem_cons_self,rfl⟩) w rfl)

private theorem marked_direction (bnd : Nat) {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      permittedSearch bnd k (zs.map project)=true) :
    pairTry k (permittedSearch bnd k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem marked_complete (bnd : Nat) {m S} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → permittedSearch bnd fuel (ws.map project)=true := by
  classical
  induction run with
  | stop permitted =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    have good := head_allowed rep (fun _ eq => eq.symm ▸ permitted)
    cases fuel <;> simp [permittedSearch,good,target,hit]
  | @step m U a b admissible kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail.live
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail.live
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → permittedSearch bnd k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := marked_direction bnd kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (permittedSearch bnd k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply marked_direction bnd (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (permittedSearch bnd k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [permittedSearch,head_allowed rep admissible,Bool.true_and,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench

namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def MarkSupport (bnd : Nat) (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ permittedSearch bnd k out=true

private theorem marked_support_from (bnd : Nat) {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, MarkSupport bnd k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail.live d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail.live (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact marked_complete bnd tail k enough out d ro

theorem marked_step (bnd : Nat) {m k S} {ws : List Wire} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      MarkSupport bnd k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b admissible op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.live.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact marked_support_from bnd op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply marked_support_from bnd (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem allowed_head {bnd k w ws} (yes : permittedSearch bnd k (w::ws)=true) : bnd≤rankSignal w := by
  cases k <;> simp only [permittedSearch,headOK,Bool.and_eq_true,decide_eq_true_eq] at yes <;> exact yes.1

end CoNatBench
namespace CoThetaSeven
open CoNatBench CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)
theorem marked_conflict (bnd label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : MarkSupport bnd 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, permitPrefix bnd label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  have certified : bnd≤rankSignal (wordGate op (nth (firstWords label) a) (nth (firstWords label) b)) := allowed_head yes
  simp only [permitPrefix,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,Nat.not_lt_of_ge certified,cov,yes]

theorem marked_after (bnd : Nat) (i : Fin 13) (checks : ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true) :
    ∀ {m S}, Marked (allowedWire bnd) (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False := by
  intro m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := marked_step bnd live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := marked_conflict bnd (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks j))

theorem marked_blocks (bnd : Nat) (i : Fin 13) (tests : ∀ b : Fin 38,
    permitBlock bnd (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true := by
  intro j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes


open CoThetaNine (SmallInput vertices7 ans7 toRows numeric_target)
theorem safe_after (r9 : RawNine) (bnd : Nat) (i : Fin 13)
    (tests : ∀ j : Fin 448, CoNatBench.permitPrefix bnd (numbers.getD i.val 0) j.val=true)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) (ok : ∀ w∈ws, CoNatBench.allowedWire bnd (restrict toRows w)) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  have permit : ∀ w∈ws.map (restrict toRows), CoNatBench.allowedWire bnd w := by
    intro w hw
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp hw
    exact eq ▸ ok a ha
  obtain ⟨k,S,le,live,sub⟩ := rewindMarked (run.map_rows toRows) zero permit
    (Marked.stop (permit _ goal)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live.live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live.live (by omega) raw
  · exact marked_after bnd i tests live (by omega) extra

end CoThetaSeven

namespace CoThetaFixedOrbit
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7)
open CoThetaSix (minorLift minor_off)
open CoThetaSeven (tag picked rotation numbered raw_mem rowPerm)

def rawGate (x y : Fin 7) (k : Kind) : TraceGate SmallInput := ⟨k,raw7 x,raw7 y⟩

theorem fresh_data (k : Kind) : ∀ (x y : Fin 7), x≠y →
    (∃ r : SmallInput, (rawGate x y k).value r ≠ false) ∧
    ∀ j : Fin 7, ∃ r : SmallInput, (rawGate x y k).value r ≠ raw7 j r := by
  cases k <;> decide +kernel

theorem head_fresh (x y : Fin 7) (k : Kind) (xy : x≠y) :
    (rawGate x y k).value∉vertices7 := by
  intro h
  rcases List.mem_cons.mp h with z|other
  · obtain ⟨r,off⟩ := (fresh_data k x y xy).1
    exact off (congrFun z r)
  · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
    obtain ⟨r,ne⟩ := (fresh_data k x y xy).2 j
    exact ne (congrFun eq.symm r)

def RawNine : Prop := ∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws
def PostNine (i : Fin 13) : Prop := ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem named_trace {x y : Fin 7} {k : Kind} (xy : x≠y)
    {n ws} (run : Free ((rawGate x y k).value::vertices7) n ws) (hit : ans7∈ws) :
    ∃ clean, sufficient vertices7 ans7 (rawGate x y k::clean) ∧
      freshTrace vertices7 (rawGate x y k::clean) ∧ clean.length≤n := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,ok,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  exact ⟨clean,⟨⟨raw_mem x,raw_mem y,ok.1⟩,ok.2⟩,⟨head_fresh x y k xy,fresh⟩,by omega⟩

theorem dispatch (x y : Fin 7) (k : Kind) (xy : x≠y) {n ws}
    (run : Free ((rawGate x y k).value::vertices7) n ws) (small : n≤9) (hit : ans7∈ws) :
    if tag x y k < 2 then RawNine else PostNine (picked (tag x y k)) := by
  classical
  let g := rawGate x y k
  obtain ⟨gs,ok,fresh,le⟩ := named_trace xy run hit
  change sufficient vertices7 ans7 (g::gs) at ok
  change freshTrace vertices7 (g::gs) at fresh
  have size : (g::gs).length≤10 := by simp only [List.length_cons]; omega
  have rx : reads g (raw7 x) := Or.inl rfl
  have ry : reads g (raw7 y) := Or.inr rfl
  let t := tag x y k
  change (if t<2 then _ else _)
  have rule := CoThetaSeven.dispatch_rules k x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  by_cases a : t=0
  · rw [if_pos a] at rule
    rw [if_pos (by omega : t<2)]
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind k (raw7 x (minorLift x r)) (raw7 y (minorLift x r))=false
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy rx ry rule.1 drop
    exact ⟨m,vs,by omega,rest,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      rw [if_pos (by omega : t<2)]
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind k (raw7 x (minorLift y r)) (raw7 y (minorLift y r))=false
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy.symm ry rx rule.1 drop
      exact ⟨m,vs,by omega,rest,out⟩
    · rw [if_neg b] at rule
      rw [if_neg (by omega : ¬t<2)]
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := funext rule
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [CoThetaSeven.raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨vs,newRun,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (CoThetaSeven.perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact ⟨_,vs,by omega,newRun,goal⟩

end CoThetaFixedOrbit
namespace CoThetaCycleFive
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)
open CoThetaSeven (read_twice raw_mem)

def roots : List Wire := [
(0xffffffff800ffe003ff800fffffc007ff001ffffffffffe003fffff001ffc007ff001ffc007ff001fffff800ffe003ffffffffffc007ff,0xfffffffd20a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a),
(0xfffffffffff000003fffff001ffffffffffe003ff800fffffc007ffffe000007ffffe000007ffffe003ffffffffffc007ff001fffff800,0xfffffffe04c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c),
(0x3fffffffe000007fffffffc00000fffffffffffffffffff800000000007fffffffc00000ffffffff800001ffffffff,0x490921242484909212424849092124248490921242484909212424849092124248490921242484909212424849092124248490),
(0xffffffffffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0xe01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
(0xffffffffffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700)]
def basis : CoNatBench.essentialBasis roots := CoThetaSix.basisAt_sound roots [4, 15, 1, 34, 90] (by decide +kernel)
theorem nd : roots.Nodup := by decide +kernel
theorem small : CoNatBench.guardedSearch 6 (roots.map CoNatBench.project)=false := by decide +kernel

def indexAt (v : Fin 7) : Option Nat := match v.val with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 5 => some 3 | 6 => some 4 | _ => none

def column (vertex : Fin 7) : Wire := match indexAt vertex with
  | none => CoThetaBits.zero
  | some n => roots.getD n CoThetaBits.zero
def liftRows (r : Row) : SmallInput := pack (fun j => den (column j) r)

def cycleGraph : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (column 0) (column 2)) (gate .conj (column 1) (column 2)))
    (gate .conj (column 0) (column 3))) (gate .conj (column 3) (column 4)))
    (gate .conj (column 1) (column 4))) (gate .conj (column 0) (column 5)))
    (gate .conj (column 5) (column 6))) (gate .conj (column 1) (column 6))


theorem table : cycleGraph=CoThetaBits.target := by decide +kernel

theorem input (j : Fin 7) : restrict liftRows (raw7 j)=den (column j) :=
  funext (fun r => unpack (fun v => den (column v) r) j)

theorem goal : restrict liftRows ans7=den CoThetaBits.target := by
  funext r
  change ans7 (liftRows r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (liftRows r))=(fun j => den (column j) r) :=
    funext (fun j => congrFun (input j) r)
  rw [values]
  have equality := congrFun (congrArg den table) r
  simp only [cycleGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem known : ∀ w∈vertices7, restrict liftRows w∈absentBit::roots.map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [input]
    cases h : indexAt j with
    | none => simp [column,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : roots[n]? with
      | none => simp [column,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [column,h,List.getD_eq_getElem?_getD,hn,inList]

theorem residual {gs : List (TraceGate SmallInput)} (ok : sufficient vertices7 ans7 gs) :
    7≤remaining liftRows gs := by
  obtain ⟨ws,run,all⟩ := restrict_trace liftRows gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self known
  have h := all ans7 ok.2
  rw [goal] at h
  have yes := CoNatBench.table_bound basis nd run h small
  omega

def joint (a b : Bool) (j : Fin 32) : SmallInput :=
  pack (fun i => if i=3 then a else if i=4 then b else j.val.testBit ((indexAt i).getD 0))

theorem separation : ∀ a b c d : Bool, (a,b)≠(c,d) →
    ∃ j : Fin 32, ans7 (joint a b j)≠ans7 (joint c d j) := by decide +kernel

theorem panel_fixed (a b c d : Bool) (j : Fin 32) :
    agreeOutside (fun f => f=raw7 3 ∨ f=raw7 4) (joint a b j) (joint c d j) vertices7 := by
  intro f hf outside
  rcases List.mem_cons.mp hf with z|other
  · subst f
    rfl
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp other
    subst f
    have i3 : i≠3 := fun e => outside (Or.inl (congrArg raw7 e))
    have i4 : i≠4 := fun e => outside (Or.inr (congrArg raw7 e))
    simp [joint,unpack,i3,i4]

def head : TraceGate SmallInput := ⟨.disj,raw7 3,raw7 4⟩

theorem no_live_ten {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (head::gs)) (fresh : freshTrace vertices7 (head::gs))
    (budget : (head::gs).length≤10) :
    ∃ k ws, k≤gs.length ∧ Free vertices7 k ws ∧ ans7∈ws := by
  classical
  have h3 : reads head (raw7 3) := Or.inl rfl
  have h4 : reads head (raw7 4) := Or.inr rfl
  by_cases path : UsePath gs head.value ans7
  · exfalso
    have gone3 := (input 3).trans (show den (column 3)=absentBit from CoThetaBits.den_zero)
    have gone4 := (input 4).trans (show den (column 4)=absentBit from CoThetaBits.den_zero)
    have newp (g : TraceGate SmallInput) (hg : g∈head::gs) :
        g.value≠raw7 3 ∧ g.value≠raw7 4 :=
      ⟨fun e => fresh_outputs fresh g hg (e ▸ raw_mem 3),
       fun e => fresh_outputs fresh g hg (e ▸ raw_mem 4)⟩
    have head0 : restrict liftRows head.value=absentBit := by
      funext r
      change (raw7 3 (liftRows r) || raw7 4 (liftRows r))=false
      have a := congrFun gone3 r
      have b := congrFun gone4 r
      change raw7 3 (liftRows r)=false at a
      change raw7 4 (liftRows r)=false at b
      simp only [a,b,Bool.false_or]
    have nz : restrict liftRows ans7 ≠ absentBit := by
      rw [goal]
      intro e
      have bad := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    obtain ⟨other,hm,n3,n4,drop⟩ := extra_loss_on_path liftRows gone3 gone4
      (fun g hg => newp g (List.mem_cons_of_mem _ hg)) path head0
      (newp head List.mem_cons_self) nz
    let all := head::gs
    let R := readerSet all (raw7 3) ∪ readerSet all (raw7 4)
    have card3 {a b c : TraceGate SmallInput} (ha : a∈R) (hb : b∈R) (hc : c∈R)
        (ab : a≠b) (ac : a≠c) (bc : b≠c) : 3≤R.card := by
      have sub : ({a,b,c}:Finset _) ⊆ R := by
        intro g hg
        simp only [Finset.mem_insert,Finset.mem_singleton] at hg
        rcases hg with rfl|rfl|rfl
        · exact ha
        · exact hb
        · exact hc
      have ct := Finset.card_le_card sub
      simpa [ab,ac,bc] using ct
    have from3 {g} (h : g∈all) (p : reads g (raw7 3)) : g∈R :=
      Finset.mem_union_left _ (mem_readerSet.mpr ⟨h,p⟩)
    have from4 {g} (h : g∈all) (p : reads g (raw7 4)) : g∈R :=
      Finset.mem_union_right _ (mem_readerSet.mpr ⟨h,p⟩)
    obtain ⟨A,ha,r3,ah⟩ := read_twice 3 4 (by decide) head h3 h4 ok
    obtain ⟨B,hb,r4,bh⟩ := read_twice 4 3 (by decide) head h4 h3 ok
    have three : 3≤R.card := by
      by_cases same : A=B
      · subst B
        have nraw (j : Fin 7) : ans7≠raw7 j := by
          obtain ⟨r,h⟩ := CoThetaSeven.seven_not_raw j
          exact fun e => h (congrFun e r)
        obtain ⟨row,ne⟩ := CoThetaSeven.seven_diff 3 4 (by decide)
        obtain ⟨C,hc,read,ch,ca⟩ := two_joint_readers_impossible (raw7 3) (raw7 4) ans7
          vertices7 all head A h3 h4 r3 r4 (fun e => ne (congrFun e row))
          ⟨nraw 3,nraw 4⟩ ok.1 ok.2 joint
          (fun a b j => by simp [joint,unpack])
          (fun a b j => by simp [joint,unpack]) panel_fixed separation
        exact card3 (from3 List.mem_cons_self h3) (from3 ha r3)
          (read.elim (from3 hc) (from4 hc)) ah.symm ch.symm ca.symm
      · exact card3 (from3 List.mem_cons_self h3) (from3 ha r3) (from4 hb r4)
          ah.symm bh.symm same
    have saved4 := four_saved_raw_head liftRows all (raw7 3) (raw7 4) gone3 gone4 three
      ⟨other,List.mem_cons_of_mem _ hm,n3,n4,drop⟩
    have cost := residual ok
    have eq := accounted liftRows (head::gs)
    change 4 ≤ saved liftRows (head::gs) at saved4
    omega
  · exact omit_dead_head vertices7 gs head.value ans7 ok.1.2.2 ok.2 path

end CoThetaCycleFive
namespace CoThetaCycleFive
open CoThetaNine (vertices7 ans7)
open CoThetaFreeCore
theorem no_post {n ws} (run : Free (head.value::vertices7) n ws)
    (bound : n≤9) (hit : ans7∈ws) : CoThetaFixedOrbit.RawNine := by
  obtain ⟨gs,ok,fresh,le⟩ := CoThetaFixedOrbit.named_trace (x:=3) (y:=4) (k:=.disj) (by decide) run hit
  have size : (head::gs).length≤10 := by simp only [List.length_cons]; omega
  obtain ⟨j,vs,small,prog,out⟩ := no_live_ten ok fresh size
  exact ⟨j,vs,by omega,prog,out⟩
end CoThetaCycleFive

namespace CoThetaSeven
open CoNatBench CoThetaBits CoThetaFreeCore

def orbitPriority (i : Fin 13) : Nat := ([5,12,11,1,7,4,8,13,6,10,2,9,3] : List Nat).getD i.val 20

def priority (x y : Fin 7) (op : Kind) : Nat :=
  let t := tag x y op
  if t<2 then 0 else orbitPriority (picked t)

private theorem rankLeaf {z : Word} {n p r bound : Nat} (x y : Fin 7) (op : Kind)
    (hit : (z.1==n && z.2==p)=true) (less : r<bound)
    (cert : x≠y ∧ project (gate op (col x) (col y))=(n,p) ∧ priority x y op=r) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  have eq : z=(n,p) := Prod.ext (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).1) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).2)
  exact ⟨x,y,op,cert.1,cert.2.1.trans eq.symm,lt_of_eq_of_lt cert.2.2 less⟩

private theorem rankFork {c : Prop} [Decidable c] {a b bound : Nat} {P : Prop}
    (v : (if c then a else b)<bound) (left : a<bound → P) (right : b<bound → P) : P := by
  by_cases h : c
  · rw [if_pos h] at v
    exact left v
  · rw [if_neg h] at v
    exact right v

private theorem rankMatch {c : Bool} {r bound : Nat} {P : Prop}
    (v : (if c then r else 20)<bound) (cap : bound≤13) (take : c=true → r<bound → P) : P := by
  cases c with
  | false => change 20<bound at v; omega
  | true => exact take rfl v

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rankSignal_sound (bound : Nat) (cap : bound≤13) (z : Word) (bad : rankSignal z<bound) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  unfold rankSignal at bad
  exact (rankFork bad
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .leftOnly hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .rightOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .rightOnly hit smaller (by decide +kernel))))))))))))))))
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .conj hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .disj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .disj hit smaller (by decide +kernel)))))))))))))))))
end CoThetaSeven

namespace CoThetaFreeCore
variable {ρ : Type}

theorem free_compose {raw us ws : List (ρ→Bool)} {m n} (pre : Free raw m us) (post : Free us n ws) : Free raw (m+n) ws := by
  induction post with
  | start => simpa using pre
  | binary _ op ha hb ih => exact .binary ih op ha hb

end CoThetaFreeCore

namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaNine (SmallInput raw7 vertices7 ans7 toRows numeric_target)
open CoThetaBits (den col gate)

def sampleCodes : List Nat := [0, 1, 2, 3, 4, 440, 453, 466, 37, 474, 18, 485, 5, 493, 498, 507, 40, 6, 510, 521, 7, 528, 537, 541, 544, 557, 562, 567, 570, 580, 583, 586, 151, 587, 21, 597, 8, 604, 609, 617, 113, 620, 52, 624, 9, 626, 627, 633, 79, 634, 641, 649, 94, 653, 655, 657, 658, 667, 670, 672, 673, 680, 681, 682, 155, 10, 683, 693, 11, 700, 708, 712, 44, 715, 723, 730, 66, 734, 736, 738, 116, 87, 739, 743, 12, 745, 751, 752, 753, 762, 764, 767, 768, 775, 776, 777, 778, 791, 795, 799, 802, 812, 815, 818, 819, 828, 831, 833, 834, 841, 842, 843, 844, 853, 855, 858, 859, 866, 867, 868, 869, 873, 874, 875, 876, 877, 878, 879]
def inverseRow (r : SmallInput) : CoThetaBits.Row :=
  let q := sampleCodes.getD r.val 0
  (decide (440≤q),⟨q % 440,Nat.mod_lt _ (by decide)⟩)

theorem sample_surjective : ∀ r : SmallInput, toRows (inverseRow r)=r := by decide +kernel

theorem reflect_rows {f g : SmallInput→Bool} (h : restrict toRows f=restrict toRows g) : f=g := by
  funext r
  have e := congrFun h (inverseRow r)
  change f (toRows (inverseRow r))=g (toRows (inverseRow r)) at e
  simpa only [sample_surjective] using e

theorem raw_gate_sample (x y : Fin 7) (op : Kind) :
    restrict toRows (CoThetaFixedOrbit.rawGate x y op).value=den (gate op (col x) (col y)) := by
  rw [CoThetaBits.den_gate]
  funext r
  change applyKind op (raw7 x (toRows r)) (raw7 y (toRows r))=_
  rw [show raw7 x (toRows r)=den (col x) r from congrFun (proj_raw x) r,
    show raw7 y (toRows r)=den (col y) r from congrFun (proj_raw y) r]

theorem raw_gate_fresh (op : Kind) : ∀ x y : Fin 7, x≠y → (CoThetaFixedOrbit.rawGate x y op).value∉vertices7 := by
  cases op <;> decide +kernel

theorem reject_raw (r9 : RawNine) : ¬ CoThetaFixedOrbit.RawNine := by
  rintro ⟨h,ys,cost,reduced,goal⟩
  let raw0 := vertices7.map (restrict toRows)
  have zero : absentBit∈raw0 := List.mem_cons_self
  have endw := List.mem_map_of_mem (f:=restrict toRows) goal
  rw [numeric_target] at endw
  obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
  have rep := CoThetaBits.root_rep live (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
    subst f
    rcases List.mem_cons.mp hw with z|l
    · subst w
      exact Or.inl rfl
    · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
      subst w
      exact Or.inr ⟨j,(proj_raw j).symm⟩)
  exact r9 live (by omega) rep

theorem numbered_start (i : Fin 13) : Free vertices7 1 ((numbered i).value::vertices7) :=
  .binary .start _ (raw_mem (casesA.getD i.val 0)) (raw_mem (casesB.getD i.val 0))

theorem orbit_cap : ∀ i : Fin 13, orbitPriority i≤13 := by decide +kernel

theorem prove_post (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ j : Fin 448,
    permitPrefix (orbitPriority i) (numbers.getD i.val 0) j.val=true) : ∀ i, ¬CoThetaFixedOrbit.PostNine i := by
  have byrank : ∀ t : Nat, ∀ i : Fin 13, orbitPriority i=t → ¬CoThetaFixedOrbit.PostNine i := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro i key post
      obtain ⟨n,ws,small,run,out⟩ := post
      by_cases five : i=10
      · subst i
        exact reject_raw r9 (CoThetaCycleFive.no_post run small out)
      apply safe_after r9 (orbitPriority i) i (checks i five) run small out
      intro f hf v eq
      by_contra no
      have low : rankSignal (project v)<orbitPriority i := by omega
      obtain ⟨x,y,k,xy,word,earlier⟩ := rankSignal_sound _ (orbit_cap i) _ low
      have same : (CoThetaFixedOrbit.rawGate x y k).value=f := by
        apply reflect_rows
        rw [raw_gate_sample,project_inj word,eq]
      have whole := free_compose (numbered_start i) run
      obtain ⟨m,ys,cap,moved,sub⟩ := free_move whole hf (same ▸ raw_gate_fresh k x y xy)
      rw [←same] at moved
      have alt := CoThetaFixedOrbit.dispatch x y k xy moved (by omega) (sub _ out)
      by_cases bad : tag x y k<2
      · rw [if_pos bad] at alt
        exact reject_raw r9 alt
      · rw [if_neg bad] at alt
        have lt : orbitPriority (picked (tag x y k))<t := by simpa [priority,bad,key] using earlier
        exact ih _ lt _ rfl alt
  intro i
  exact byrank _ i rfl

theorem lower_from_ranked (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ b : Fin 38,
    permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true)
    {n ws} (run : Free vertices7 n ws) (out : ans7∈ws) : 11≤n := by
  by_contra bad
  rcases select_program run (by omega) out with raw|⟨i,post⟩
  · exact reject_raw r9 raw
  · exact prove_post r9 (fun i ne => marked_blocks _ i (checks i ne)) i post

end CoThetaSeven
namespace CoThetaProofData
open CoNatBench CoThetaSeven
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem raw_all (i : Fin 84) : guardedSearch 8 (firstWords i.val)=false := by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block0 (b : Fin 38) : permitBlock 5 0 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block1 (b : Fin 38) : permitBlock 12 1 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block2 (b : Fin 38) : permitBlock 11 2 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block5 (b : Fin 38) : permitBlock 1 5 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block6 (b : Fin 38) : permitBlock 7 6 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block9 (b : Fin 38) : permitBlock 4 9 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block10 (b : Fin 38) : permitBlock 8 10 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block13 (b : Fin 38) : permitBlock 13 13 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block14 (b : Fin 38) : permitBlock 6 14 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block45 (b : Fin 38) : permitBlock 10 45 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block65 (b : Fin 38) : permitBlock 9 65 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block69 (b : Fin 38) : permitBlock 3 69 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
theorem all_blocks (i : Fin 13) (ne : i≠10) (b : Fin 38) : permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases i
  · exact block0 b
  · exact block1 b
  · exact block2 b
  · exact block5 b
  · exact block6 b
  · exact block9 b
  · exact block10 b
  · exact block13 b
  · exact block14 b
  · exact block45 b
  · exact (ne rfl).elim
  · exact block65 b
  · exact block69 b
end CoThetaProofData

namespace CoThetaSeven

theorem checked_lower : CoThetaNine.SignedLower :=
  fun run out => lower_from_ranked (root_from_cases CoThetaProofData.raw_all) CoThetaProofData.all_blocks run out

end CoThetaSeven
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem fullGraphLower : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (prior:=boundsBefore known383) (i:=0) (hints:=0x321032124)
    (before_sound _ valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

open CoThetaFreeCore (Free norm normalizedKind normalize_unary normalize_binary applyKind)
open CoThetaNine (vtx row ans vertices)
def signedWord (a : Sig) := norm (row 0) (observe a)
theorem signedNeg (a : Sig) : signedWord (neg a) = signedWord a := by
  have eq : observe (neg a) = fun r => !(observe a r) := by
    funext r
    simp [observe,bit,neg,r.isLt]
  unfold signedWord
  rw [eq,normalize_unary]
theorem signedBin (d : Bool) (a b : Sig) :
    signedWord (bin d a b) = fun r => applyKind
      (normalizedKind d (observe a (row 0)) (observe b (row 0)))
      (signedWord a r) (signedWord b r) := by
  have eq : observe (bin d a b) = fun r => CoThetaFreeCore.base d (observe a r) (observe b r) := by
    funext r
    cases d <;> simp [observe,bit,bin,CoThetaFreeCore.base]
  unfold signedWord
  rw [eq,normalize_binary]

theorem liveSigned {T k t S} (run : Live T k t S) :
    ∀ {n ws}, Free vertices n ws → (∀ a∈S, signedWord a ∈ ws) →
      ∃ m ys, m+t=n+k ∧ Free vertices m ys ∧ signedWord T ∈ ys := by
  induction run with
  | stop hp =>
    intro n ws pre sub
    exact ⟨n,ws,by omega,pre,sub _ (Finset.mem_singleton_self _)⟩
  | @unary k t U a ha hf tail ih =>
    intro n ws pre sub
    obtain ⟨m,ys,len,after,covers⟩ := ih pre (by
      intro z hz
      rcases Finset.mem_insert.mp hz with hit | old
      · rw [hit,signedNeg]
        exact sub _ (Finset.mem_insert_self _ _)
      · exact sub _ (Finset.mem_insert_of_mem old))
    exact ⟨m,ys,by omega,after,covers⟩
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro n ws pre sub
    have left := sub a (Finset.mem_insert_self _ _)
    have right := sub b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have made := Free.binary pre (normalizedKind d (observe a (row 0)) (observe b (row 0))) left right
    obtain ⟨m,ys,len,after,covers⟩ := ih made (by
      intro z hz
      rcases Finset.mem_insert.mp hz with hit | old
      · rw [hit,signedBin]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sub _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))))
    exact ⟨m,ys,by omega,after,covers⟩

theorem originalInput (i : Fin 9) : signedWord (inputs.getD i.val zero) = vtx i := by
  funext r
  exact (by decide +kernel : ∀ (i : Fin 9) (r : Fin 512), signedWord (inputs.getD i.val zero) r = vtx i r) i r
theorem originalGoal : signedWord graph = ans := by
  funext r
  exact (by decide +kernel : ∀ r, signedWord graph r = ans r) r
theorem checkedSignedBound {m ys} (p : Free vertices m ys) (out : ans ∈ ys) : 14 ≤ m := by
  obtain ⟨gs,len,registered,eq⟩ := CoThetaFreeCore.trace_of_free p
  have lower := CoThetaNine.any_nine_lower CoThetaSeven.checked_lower (gs:=gs) ⟨registered,eq ▸ out⟩
  omega
theorem dead_start : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoThetaFreeCore (Free)
open CoThetaNine (vertices ans vtx)

private def bank3415 : Bool → List Sig
  | false => inputs
  | true => neg (inputs.getD 0 zero) :: inputs.tail

private theorem sample3415 : ∀ (b : Bool) (r : Row),
    (bank3415 b).map (bit r) = List.ofFn (fun i : Fin 9 =>
      if i = 0 then b != sample r 0 else sample r i) := by decide +kernel

private theorem raw3415 (v : Sig) (hv : v ∈ inputs) : signedWord v ∈ vertices := by
  rw [← input_list, List.mem_ofFn] at hv
  obtain ⟨i,rfl⟩ := hv
  rw [originalInput]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem flipped3415 {k t S} (run : Live graph k t S) (small : k ≤ 14)
    (sub : ∀ v ∈ S, v ∈ bank3415 true)
    (bound : ∀ {m ys}, Free vertices m ys → ans ∈ ys → 14 ≤ m) : False := by
  obtain ⟨m,ys,budget,program,out⟩ := liveSigned run (Free.start (raw:=vertices)) (by
    intro v hv
    rcases List.mem_cons.mp (sub v hv) with eq | old
    · rw [eq, signedNeg, show signedWord (inputs.getD 0 zero) = vtx 0 from originalInput (0 : Fin 9)]
      exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨0,rfl⟩)
    · exact raw3415 _ ((List.tail_sublist _).subset old))
  rw [originalGoal] at out
  have minimum := bound program out
  have none : t=0 := by omega
  obtain ⟨a,ha,h3,h2⟩ := mono_row_difference run none (r:=3) (s:=2) (by decide +kernel) (by decide +kernel)
  have impossible : (bank3415 true).all (fun z => !(bit 3 z && !(bit 2 z))) = true := by decide +kernel
  have := List.all_eq_true.mp impossible a (sub a ha)
  simp [h3,h2] at this

private theorem ordinary3415 {k t S} (run : Live graph k t S) (small : k ≤ 14)
    (sub : ∀ v ∈ S, v ∈ inputs) (deadNo : Impossible graph 14 inputs.toFinset) : False := by
  have same : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      have hm := List.mem_toFinset.mp ha
      rw [←input_list, List.mem_ofFn] at hm
      obtain ⟨i,rfl⟩ := hm
      let neighbor : Fin 9 → Nat := ![1,0,1,2,3,0,1,2,3]
      let arow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
      let brow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
      have certificate : ∀ j : Fin 9, (bit (arow j) graph != bit (brow j) graph) &&
          (inputs.all fun w => w == inputs.getD j.val zero || bit (arow j) w == bit (brow j) w) = true := by
        unfold arow brow neighbor; decide +kernel
      have hh := certificate i
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, List.all_eq_true,
        Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
      exact raw_required run inputs _ sub (arow i) (brow i) hh.1
        (fun w hw ne => (hh.2 w hw).resolve_left ne)
  exact deadNo k t small (same ▸ run)

private theorem result3415 (lower : ∀ {m ys}, Free vertices m ys → ans ∈ ys → 14 ≤ m)
    (deadNo : Impossible graph 14 inputs.toFinset) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (¬∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C b hc hs _ _
  classical
  apply Classical.byContradiction
  intro bad
  let bk := bank3415 b
  have he (r : Row) : C.eval (bk.map (bit r)) = edge (sample r) := by
    rw [show bk = bank3415 b from rfl,sample3415]
    exact Classical.not_not.mp (fun h => bad ⟨sample r,h⟩)
  have eq : (execute C.gates bk).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r _ = bit r graph
    rw [←b_read, execute_bits _ _ _ (fun g hg => (hc g hg).1)]
    exact (he r).trans (edge_table r).symm
  have mem := get_rep (execute C.gates bk) C.output
  rw [eq] at mem
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates bk hc graph_proper (mem.resolve_right (fun h => h graph_proper))
  cases b with
  | false => exact ordinary3415 run (hk.trans hs) sub deadNo
  | true => exact flipped3415 run (hk.trans hs) sub lower

end PEqualNP.Outside.L_meta_3415

theorem PEqualNP.Outside.L_meta_3415 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (¬∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3415.result3415 (@PEqualNP.Outside.L_meta_3415.checkedSignedBound) PEqualNP.Outside.L_meta_3415.dead_start
