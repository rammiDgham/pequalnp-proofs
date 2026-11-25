import PEqualNP.Defs

-- The signed-circuit semantics and live-wire construction follow L-meta-8724,
-- L-meta-1449, L-meta-1429 and L-meta-703. Input two is essential.
-- Setting it to false saves a binary gate and leaves six variables.
-- The finite blocks exclude eight binary gates on that restriction.
namespace PEqualNP.Outside.L_meta_11285_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 512 rows at once, NOT gates cost nothing.
private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux

def clean : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch extra
      (fun e s => !(ws.contains (s.headD 0)) && clean k e s) a b r)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem clean_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    clean n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [clean, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [clean, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e s => !(ws.contains (s.headD 0)) && clean k e s) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (fun e s => !(ws.contains (s.headD 0)) && clean k e s) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply Bool.and_eq_true_iff.mpr
        constructor
        · simpa [List.headD, List.contains_eq_mem] using hout
        · apply ih _ _ hnd _ hl
          simp; omega
      simp only [clean, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
def full : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mask : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def aim : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def width : ℕ := 0x10000000000000000000000000000000000000000000000000000000000000000

def cutWord (v : ℕ) : ℕ := ((v >>> 256) ^^^ v) % width
def maskOf (v : List ℕ) := v.foldr (fun w s => cutWord w ||| s) 0
def opsN (a b : ℕ) := [a &&& b, a ||| b, a &&& (mask-b), b &&& (mask-a)]
def leaf (ws : List ℕ) := ws == [aim] || ws == [full]
def explore (extra : ℕ) (call : ℕ → List ℕ → Bool) (ws : List ℕ)
    (a b : ℕ) (r : List ℕ) : Bool :=
  let lo := maskOf r
  let a0 := cutWord a
  let b0 := cutWord b
  (opsN a b).any (fun w =>
    !ws.contains w &&
    (let v := cutWord w ||| lo
     (v == full && call extra (w::r)) ||
      (extra != 0 && ((v ||| a0 == full && call (extra-1) (w::a::r)) ||
                      (v ||| b0 == full && call (extra-1) (w::b::r)))) ||
      (extra ≥ 2 && v ||| a0 ||| b0 == full && call (extra-2) (w::a::b::r))))
def walk : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => leaf ws
  | k+1, e, ws => leaf ws || (pairs ws).any (fun (a,b,r) => explore e (walk k) ws a b r)
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck

def asNs (ws : List W) : List ℕ := ws.map BitVec.toNat
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem nat_eq {n : ℕ} (x y : BitVec n) : (x.toNat == y.toNat) = (x == y) := by rfl
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem mask_val : mask = 2^512-1 := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem width_val : width = 2^256 := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem full_val : full = (-1 : BitVec 256).toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem aim_val : aim = goal.toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem opp_val : full = (~~~goal).toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cut_as (w : W) : cutWord w.toNat = (sep w).toNat := by
  simp only [cutWord,sep,BitVec.toNat_setWidth,BitVec.toNat_xor,BitVec.toNat_ushiftRight,width_val]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem masks_as (ws : List W) : maskOf (asNs ws) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    change (cutWord x.toNat ||| maskOf (asNs xs)) = (sep x ||| cuts xs).toNat
    rw [ih,cut_as,BitVec.toNat_or]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_as (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp [opsN,ops,mask_val]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem contains_as (ws : List W) (w : W) : (asNs ws).contains w.toNat = ws.contains w := by
  induction ws with
  | nil => rfl
  | cons v vs ih =>
    simpa only [asNs,List.map_cons,List.contains_cons,nat_eq] using
      congrArg (fun t => (w == v) || t) ih
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem leaf_as (ws : List W) : leaf (asNs ws) = (ws == [goal] || ws == [~~~goal]) := by
  rcases ws with _|⟨v,_|⟨z,zs⟩⟩
  · rfl
  · simp only [leaf,asNs,List.map_cons,List.map_nil,aim_val,opp_val,List.cons_beq_cons,nat_eq]
    rfl
  · simp only [leaf,asNs,List.map_cons,List.cons_beq_cons,List.beq_nil_eq,List.isEmpty_cons,Bool.and_false]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem single_map {α β : Type} (f : α → β) (xs : List α) :
    singles (xs.map f) = (singles xs).map (fun (x,r) => (f x,r.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [singles,ih,List.map_map,Function.comp_def]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pair_map {α β : Type} (f : α → β) (xs : List α) :
    pairs (xs.map f) = (pairs xs).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs,ih,single_map,List.map_map,Function.comp_def]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem explore_as (e : ℕ) (call : ℕ → List ℕ → Bool) (ws : List W) (a b : W) (r : List W) :
    explore e call (asNs ws) a.toNat b.toNat (asNs r) =
       dispatch e (fun n s => !(ws.contains (s.headD 0)) && call n (asNs s)) a b r := by
  simp only [explore,dispatch,ops_as,masks_as,List.any_map,Function.comp_def]
  apply List.any_congr rfl
  intro w
  simp only [contains_as,cut_as,full_val,← BitVec.toNat_or,nat_eq,List.headD_cons]
  cases h : ws.contains w <;> simp [h,asNs]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem walk_as (k e : ℕ) (ws : List W) : walk k e (asNs ws) = clean k e ws := by
  induction k generalizing e ws with
  | zero => exact leaf_as _
  | succ k ih =>
    simp only [walk,clean,leaf_as]
    simp only [asNs,pair_map,List.any_map,Function.comp_def]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    change explore e (walk k) (asNs ws) a.toNat b.toNat (asNs r) = _
    rw [explore_as]
    simp only [ih]
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
abbrev CallState := ℕ × List ℕ
def keepIf (b : Bool) (xs : List CallState) : List CallState := if b then xs else []
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem any_keepIf (b : Bool) (xs : List CallState) (f : CallState → Bool) :
    (keepIf b xs).any f = (b && xs.any f) := by cases b <;> simp [keepIf]
def nextFor (ws : List ℕ) (e a b : ℕ) (r : List ℕ) (w : ℕ) : List CallState :=
  let v := cutWord w ||| maskOf r
  let ca := cutWord a
  let cb := cutWord b
  keepIf (!ws.contains w) (
    keepIf (v == full) [(e,w::r)] ++
    keepIf (e != 0) (keepIf ((v ||| ca) == full) [(e-1,w::a::r)] ++
                      keepIf ((v ||| cb) == full) [(e-1,w::b::r)]) ++
    keepIf (decide (e ≥ 2) && (v ||| ca ||| cb == full)) [(e-2,w::a::b::r)])
def nextList (e : ℕ) (ws : List ℕ) : List CallState :=
  (pairs ws).flatMap (fun (a,b,r) => (opsN a b).flatMap (nextFor ws e a b r))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem any_next (e : ℕ) (call : ℕ → List ℕ → Bool) (ws : List ℕ) (a b : ℕ) (r : List ℕ) :
    explore e call ws a b r =
      ((opsN a b).flatMap (nextFor ws e a b r)).any (fun q => call q.1 q.2) := by
  simp only [explore,List.any_flatMap]
  apply List.any_congr rfl
  intro w
  simp only [nextFor,any_keepIf,List.any_append,List.any_cons,List.any_nil,Bool.or_false]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem split_walk {k e : ℕ} {ws : List ℕ} {fr : List CallState}
    (terminal : leaf ws = false) (cover : nextList e ws = fr)
    (rest : ∀ v ∈ fr, walk k v.1 v.2 = false) : walk (k+1) e ws = false := by
  have split : (pairs ws).any (fun (a,b,r) => explore e (walk k) ws a b r) =
      (nextList e ws).any (fun q => walk k q.1 q.2) := by
    simp only [nextList,List.any_flatMap]
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    simpa only [List.any_flatMap] using any_next e (walk k) ws a b r
  rw [walk,terminal,Bool.false_or,split,cover]
  simpa only [List.any_eq_false,Bool.not_eq_true] using rest
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
def AllRejected (k : ℕ) (l : List CallState) : Prop := ∀ v ∈ l, walk k v.1 v.2 = false
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem emptyOk (k : ℕ) : AllRejected k [] := by simp [AllRejected]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem consOk {k e : ℕ} {ws : List ℕ} {l : List CallState}
    (h : walk k e ws = false) (t : AllRejected k l) : AllRejected k ((e,ws)::l) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl|hv
  · exact h
  · exact t _ hv
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem entersOnly {n : ℕ} (v : List W) (hn : v.Nodup)
    (start : v.sublists.filter (fun w => decide (w.length ≤ n + 1) && (cuts w == -1)) = [v])
    (reject : walk n (n+1-v.length) (asNs v) = false)
    (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t n v.toFinset) : False := by
  classical
  obtain ⟨s,hs,hl⟩ := compress run
  let u := v.filter (· ∈ s)
  have eq : u.toFinset = s := by
    ext w
    simp only [u,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hn' : u.Nodup := hn.filter _
  have hl' : live basicOps t n u.toFinset := eq.symm ▸ hl
  have room := live_card hl'
  rw [List.toFinset_card_of_nodup hn'] at room
  have m : u ∈ v.sublists.filter (fun w => decide (w.length ≤ n+1) && (cuts w == -1)) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr (List.filter_sublist ..),by simp [room,cuts_full ht hl']⟩
  have uv : u = v := List.mem_singleton.mp (start ▸ m)
  have hit := clean_complete ht n u (n+1-u.length) hn' (by omega) hl'
  rw [uv,←walk_as] at hit
  exact Bool.noConfusion (reject.symm.trans hit)
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checkedBlock {k : ℕ} {l : List CallState}
    (h : l.all (fun q => !(walk k q.1 q.2)) = true) : AllRejected k l := by
  intro q hq
  simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h q hq
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem appendOk {k : ℕ} {l r : List CallState} (hl : AllRejected k l) (hr : AllRejected k r) :
    AllRejected k (l++r) := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact hl q h
  · exact hr q h
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity NatCheck
def graph (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,6]⟩, ⟨.or,[3,4]⟩, ⟨.and,[7,8]⟩, ⟨.or,[5,6]⟩, ⟨.or,[0,2]⟩, ⟨.or,[3,11]⟩, ⟨.and,[10,12]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,14]⟩, ⟨.or,[9,13]⟩, ⟨.or,[15,16]⟩],17⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem smallLegal : ∀ g ∈ smallCircuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [smallCircuit]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
theorem smallEval : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = graph x := by decide +kernel

def inputs7 : List W := [0x570cf5552cb4d52e0296678962589625897fc94920a186bab77efc44447c824f00000fff00000001f000000000000000001fc000000003f8933e7800003c000f,0xab555aaa50410a0035febf92a4a92a4affeac2821942194cdbab68bc8bfc243000ffffff000000fe007e0380000000007fe00000f8007ffc9bab683c03fc0030,0x10000000000000000000000000000000000000000000000000000000000000000000,0xcdaaa0cf851a4052c92bdfa4c9324dff92a15414420ce41f1dcfbd093fc541c1fffff00000003f0000001f80000001ff80000000001ffc0708c180003fc001c0,0x323333331a6023851e4dfcc711c7fe9324c5a0e08c73086fe1f3ca13fc8a0e12ff000000000fc0000001fc000007fe000000000007ff800360408003fc000e00,0x3cc3cc3ce0038c186ff1e9781ffc711c471607071384318ffe03f3e3d11070a40000000003f000000f81e0001ff800000000003f07e00000640003c3c0007000,0xc0fc0fc0038c30e18fff127ffe0781e078183838e418420ffffc03fe2223890800000000fc0000000ffe007fe00000000000003ff8000000040003fc00038000]
def inputs6 : List W := [0x570cf5552cb4d52e0296678962589625897fc94920a186bab77efc44447c924f00000fff00000001f000000000000000001fc000000003f8933e7800003c000f,0xab555aaa50410a0035febf92a4a92a4affeac2821942194cdbab68bc8bfc243000ffffff000000fe007e0380000000007fe00000f8007ffc9bab683c03fc0030,0xcdaaa0cf851a4052c92bdfa4c9324dff92a15414420ce41f1dcfbd093fc541c1fffff00000003f0000001f80000001ff80000000001ffc0708c180003fc001c0,0x323333331a6023851e4dfcc711c7fe9324c5a0e08c73086fe1f3ca13fc8a0e12ff000000000fc0000001fc000007fe000000000007ff800360408003fc000e00,0x3cc3cc3ce0038c186ff1e9781ffc711c471607071384318ffe03f3e3d11070a40000000003f000000f81e0001ff800000000003f07e00000640003c3c0007000,0xc0fc0fc0038c30e18fff127ffe0781e078183838e418420ffffc03fe2223890800000000fc0000000ffe007fe00000000000003ff8000000040003fc00038000]
section Projection
variable {α β : Type} [DecidableEq α] [DecidableEq β]
lemma build_mono {ops : α → α → Finset α} {g : α} {k : ℕ} {s t : Finset α}
    (h : build ops g k s) (hs : s ⊆ t) : build ops g k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with h | ⟨a,ha,b,hb,hne,z,hz,next⟩
    · exact Or.inl (ih h hs)
    · exact Or.inr ⟨a,hs ha,b,hs hb,hne,z,hz,ih next (Finset.insert_subset_insert _ hs)⟩

def dead (p : α → β) (e : β) (s : Finset α) := (s.filter fun w => p w = e).card
def avail (p : α → β) (e : β) (s : Finset α) := (s.image p).erase e

omit [DecidableEq α] in
lemma mem_avail {p : α → β} {e b : β} {s : Finset α} :
    b ∈ avail p e s ↔ b ≠ e ∧ ∃ a ∈ s, p a = b := by simp [avail]

lemma dead_insert_le (p : α → β) (e : β) (a : α) (s : Finset α) :
    dead p e (insert a s) ≤ dead p e s + if p a = e then 1 else 0 := by
  by_cases h : p a = e
  · simpa [dead,Finset.filter_insert,h] using Finset.card_insert_le a (s.filter fun w => p w = e)
  · simp [dead,Finset.filter_insert,h]

lemma dead_insert_eq (p : α → β) (e : β) (a : α) (s : Finset α) (ha : a ∉ s) :
    dead p e (insert a s) = dead p e s + if p a = e then 1 else 0 := by
  by_cases h : p a = e <;> simp [dead,Finset.filter_insert,h,ha]

theorem project_live {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (p : α → β) (e : β) (g : α) (hg : p g ≠ e)
    (collapse : ∀ a b z, z ∈ ops a b → p a = e → p b = e → p z = e)
    (step : ∀ a b z, z ∈ ops a b → p z ≠ e → p z ≠ p a → p z ≠ p b →
      p a ≠ e ∧ p b ≠ e ∧ p a ≠ p b ∧ p z ∈ ops' (p a) (p b))
    {k : ℕ} {s : Finset α} (h : live ops g k s) :
    ∃ j, j + dead p e s ≤ k ∧ build ops' (p g) j (avail p e s) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    subst s
    refine ⟨0, by simp [dead,hg], ?_⟩
    exact mem_avail.mpr ⟨hg,g,by simp,rfl⟩
  | succ k ih =>
    rcases h with h | ⟨a,ha,b,hb,_,z,hz,hnew,r,hs,tail⟩
    · obtain ⟨j,budget,done⟩ := ih h
      exact ⟨j,by omega,done⟩
    · obtain ⟨j,budget,done⟩ := ih tail
      have zr : z ∉ r := fun hm => hnew (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      have rs : r ⊆ s := fun _ hm => hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)
      rw [dead_insert_eq p e z r zr] at budget
      have ba := dead_insert_le p e a (insert b r)
      rw [← hs] at ba
      have bb := dead_insert_le p e b r
      have tailSub : avail p e (insert z r) ⊆ insert (p z) (avail p e s) := by
        intro y hy
        obtain ⟨ye,w,hw,rfl⟩ := mem_avail.mp hy
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · simp
        · exact Finset.mem_insert_of_mem (mem_avail.mpr ⟨ye,w,rs hwr,rfl⟩)
      by_cases trivial : p z = e ∨ p z = p a ∨ p z = p b
      · have lift : avail p e (insert z r) ⊆ avail p e s := by
          intro y hy
          obtain ⟨ye,w,hw,rfl⟩ := mem_avail.mp hy
          rcases Finset.mem_insert.mp hw with rfl | hwr
          · rcases trivial with he | hea | heb
            · contradiction
            · exact mem_avail.mpr ⟨ye,a,ha,hea.symm⟩
            · exact mem_avail.mpr ⟨ye,b,hb,heb.symm⟩
          · exact mem_avail.mpr ⟨ye,w,rs hwr,rfl⟩
        refine ⟨j,?_,build_mono done lift⟩
        by_cases ae : p a = e <;> by_cases be : p b = e <;> by_cases ze : p z = e <;>
          simp [ae,be,ze] at ba bb budget <;> first | omega | exact False.elim (ze (collapse a b z hz ae be))
      · simp only [not_or] at trivial
        obtain ⟨ae,be,ab,valid⟩ := step a b z hz trivial.1 trivial.2.1 trivial.2.2
        refine ⟨j+1,?_,Or.inr ⟨p a,mem_avail.mpr ⟨ae,a,ha,rfl⟩,p b,mem_avail.mpr ⟨be,b,hb,rfl⟩,
          ab,p z,valid,build_mono done tailSub⟩⟩
        simp [ae,be,trivial.1] at ba bb budget
        omega

end Projection
def mark : W := 0x10000000000000000000000000000000000000000000000000000000000000000000
def selected (j : Fin 512) : Fin 512 := if mark[j.val] then 258 else j
def patch (w : W) := if w[258] then w ||| mark else w &&& ~~~mark
private lemma patch_bit (w : W) (j : ℕ) (hj : j < 512) :
    (patch w)[j] = w[(selected ⟨j,hj⟩).val] := by
  cases a : w[258] <;> cases b : mark[j] <;> simp [patch,selected,a,b]
private lemma patch_not (u : W) : patch (~~~u) = ~~~patch u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [patch_bit,BitVec.getElem_not]
private lemma patch_ops (a b z : W) (hz : z ∈ basicOps a b) : patch z ∈ basicOps (patch a) (patch b) := by
  have hand (u v : W) : patch (u &&& v) = (patch u &&& patch v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [patch_bit,BitVec.getElem_and]
  have hor (u v : W) : patch (u ||| v) = (patch u ||| patch v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [patch_bit,BitVec.getElem_or]
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand,hor,patch_not]
set_option maxRecDepth 6000 in
private lemma left0 (a b z : W) (hz : z ∈ basicOps a b) (h : a = 0) : z = 0 ∨ z = b := by
  subst a
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact Or.inl BitVec.zero_and
  · exact Or.inr BitVec.zero_or
  · exact Or.inl BitVec.zero_and
  · exact Or.inr BitVec.and_allOnes
set_option maxRecDepth 6000 in
private lemma right0 (a b z : W) (hz : z ∈ basicOps a b) (h : b = 0) : z = 0 ∨ z = a := by
  subst b
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact Or.inl BitVec.and_zero
  · exact Or.inr BitVec.or_zero
  · exact Or.inr BitVec.and_allOnes
  · exact Or.inl BitVec.zero_and
set_option maxRecDepth 6000 in
private lemma same0 (a b z : W) (hz : z ∈ basicOps a b) (h : a = b) : z = 0 ∨ z = a := by
  subst b
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact Or.inr BitVec.and_self
  · exact Or.inr BitVec.or_self
  · exact Or.inl (BitVec.and_not_self _)
  · exact Or.inl (BitVec.and_not_self _)
private lemma projected_live {k : ℕ} {s : Finset W} {g : W} (gn : patch g ≠ 0) (run : live basicOps g k s) :
    ∃ j, j + dead patch 0 s ≤ k ∧ build basicOps (patch g) j (avail patch 0 s) := by
  apply project_live (p := patch) (e := 0) (g := g) gn _ _ run
  · intro a b z hz ha hb
    exact (left0 _ _ _ (patch_ops a b z hz) ha).elim id (fun h => h.trans hb)
  · intro a b z hz ne za zb
    have h := patch_ops a b z hz
    exact ⟨fun ha => (left0 _ _ _ h ha).elim ne zb,fun hb => (right0 _ _ _ h hb).elim ne za,
      fun eq => (same0 _ _ _ h eq).elim ne za,h⟩
private lemma raised {g : W} {w : Finset W} {a b : ℕ} (h : build basicOps g a w) (le : a ≤ b) :
    build basicOps g b w := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem exclude_six (cert : walk 8 3 (asNs inputs6) = false) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 9 inputs7.toFinset) : False := by
  obtain ⟨s,sub,liveRun⟩ := compress run
  have gd : differs 12 t := by rcases ht with rfl|rfl <;> unfold differs <;> decide +kernel
  obtain ⟨w,ws,d⟩ := live_separates (differs 12) gd (ops_differs 12) liveRun
  have single : inputs7.filter (fun z => z.getLsbD 12 != z.getLsbD 268) = [mark] := by decide +kernel
  have singled : w ∈ inputs7.filter (fun z => z.getLsbD 12 != z.getLsbD 268) :=
    List.mem_filter.mpr ⟨List.mem_toFinset.mp (sub ws),by simpa [differs,ne_comm] using d⟩
  have forced : mark ∈ s := (List.mem_singleton.mp (single ▸ singled)) ▸ ws
  have loss : 0 < dead patch 0 s := Finset.card_pos.mpr ⟨mark,Finset.mem_filter.mpr ⟨forced,by decide +kernel⟩⟩
  have teq : patch t = t := by rcases ht with rfl|rfl <;> decide +kernel
  have tn : patch t ≠ 0 := by rw [teq]; rcases ht with rfl|rfl <;> decide +kernel
  obtain ⟨k,budget,done⟩ := projected_live tn liveRun
  rw [teq] at done
  have pool : (inputs7.map patch).filter (· != 0) = inputs6 := by decide +kernel
  have supply : avail patch 0 s ⊆ inputs6.toFinset := by
    intro v hv
    obtain ⟨nz,x,hx,rfl⟩ := mem_avail.mp hv
    rw [←pool]
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨x,List.mem_toFinset.mp (sub hx),rfl⟩,by simpa using nz⟩)
  apply entersOnly inputs6 (by decide +kernel) (n := 8) _ cert t ht (raised (build_mono done supply) (by omega))
  decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
theorem sample : ∀ j : Fin 512, graph (fun i => (inputs7.getD i.val 0)[j.val]) = goal[j.val] := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ten_binary (cert : walk 8 3 (asNs inputs6) = false) (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs7, holds inputs7.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (inputs7.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 7 => bit k (inputs7.getD i.val 0)) =
        inputs7.map (bit k) := by
      apply List.ext_getElem (by simp [inputs7])
      intro i hi hj
      have hlt : i < inputs7.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs7.map (bit k)) = bit k goal
    rw [← same, he]
    exact sample k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs7 inputs7.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs7.toFinset) :
      build basicOps t b inputs7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact exclude_six cert ht (lift low run)
end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck.Delete2
def v0 : ℕ := 0x570cf5552cb4d52e0296678962589625897fc94920a186bab77efc44447c924f00000fff00000001f000000000000000001fc000000003f8933e7800003c000f
def v1 : ℕ := 0xab555aaa50410a0035febf92a4a92a4affeac2821942194cdbab68bc8bfc243000ffffff000000fe007e0380000000007fe00000f8007ffc9bab683c03fc0030
def v2 : ℕ := 0xcdaaa0cf851a4052c92bdfa4c9324dff92a15414420ce41f1dcfbd093fc541c1fffff00000003f0000001f80000001ff80000000001ffc0708c180003fc001c0
def v3 : ℕ := 0x323333331a6023851e4dfcc711c7fe9324c5a0e08c73086fe1f3ca13fc8a0e12ff000000000fc0000001fc000007fe000000000007ff800360408003fc000e00
def v4 : ℕ := 0x3cc3cc3ce0038c186ff1e9781ffc711c471607071384318ffe03f3e3d11070a40000000003f000000f81e0001ff800000000003f07e00000640003c3c0007000
def v5 : ℕ := 0xc0fc0fc0038c30e18fff127ffe0781e078183838e418420ffffc03fe2223890800000000fc0000000ffe007fe00000000000003ff8000000040003fc00038000
def wires0 : List ℕ := [v0,v1,v2,v3,v4,v5]
def block0 : List CallState := ((nextList 3 wires0).drop 0).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed0 : AllRejected 7 block0 := checkedBlock (by decide +kernel)
def block1 : List CallState := ((nextList 3 wires0).drop 1).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed1 : AllRejected 7 block1 := checkedBlock (by decide +kernel)
def block2 : List CallState := ((nextList 3 wires0).drop 2).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed2 : AllRejected 7 block2 := checkedBlock (by decide +kernel)
def block3 : List CallState := ((nextList 3 wires0).drop 3).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed3 : AllRejected 7 block3 := checkedBlock (by decide +kernel)
def block4 : List CallState := ((nextList 3 wires0).drop 4).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed4 : AllRejected 7 block4 := checkedBlock (by decide +kernel)
def block5 : List CallState := ((nextList 3 wires0).drop 5).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed5 : AllRejected 7 block5 := checkedBlock (by decide +kernel)
def block6 : List CallState := ((nextList 3 wires0).drop 6).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed6 : AllRejected 7 block6 := checkedBlock (by decide +kernel)
def block7 : List CallState := ((nextList 3 wires0).drop 7).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed7 : AllRejected 7 block7 := checkedBlock (by decide +kernel)
def block8 : List CallState := ((nextList 3 wires0).drop 8).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed8 : AllRejected 7 block8 := checkedBlock (by decide +kernel)
def block9 : List CallState := ((nextList 3 wires0).drop 9).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed9 : AllRejected 7 block9 := checkedBlock (by decide +kernel)
def block10 : List CallState := ((nextList 3 wires0).drop 10).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed10 : AllRejected 7 block10 := checkedBlock (by decide +kernel)
def block11 : List CallState := ((nextList 3 wires0).drop 11).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed11 : AllRejected 7 block11 := checkedBlock (by decide +kernel)
def block12 : List CallState := ((nextList 3 wires0).drop 12).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed12 : AllRejected 7 block12 := checkedBlock (by decide +kernel)
def block13 : List CallState := ((nextList 3 wires0).drop 13).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed13 : AllRejected 7 block13 := checkedBlock (by decide +kernel)
def block14 : List CallState := ((nextList 3 wires0).drop 14).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed14 : AllRejected 7 block14 := checkedBlock (by decide +kernel)
def block15 : List CallState := ((nextList 3 wires0).drop 15).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed15 : AllRejected 7 block15 := checkedBlock (by decide +kernel)
def block16 : List CallState := ((nextList 3 wires0).drop 16).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed16 : AllRejected 7 block16 := checkedBlock (by decide +kernel)
def block17 : List CallState := ((nextList 3 wires0).drop 17).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed17 : AllRejected 7 block17 := checkedBlock (by decide +kernel)
def block18 : List CallState := ((nextList 3 wires0).drop 18).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed18 : AllRejected 7 block18 := checkedBlock (by decide +kernel)
def block19 : List CallState := ((nextList 3 wires0).drop 19).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed19 : AllRejected 7 block19 := checkedBlock (by decide +kernel)
def block20 : List CallState := ((nextList 3 wires0).drop 20).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed20 : AllRejected 7 block20 := checkedBlock (by decide +kernel)
def block21 : List CallState := ((nextList 3 wires0).drop 21).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed21 : AllRejected 7 block21 := checkedBlock (by decide +kernel)
def block22 : List CallState := ((nextList 3 wires0).drop 22).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed22 : AllRejected 7 block22 := checkedBlock (by decide +kernel)
def block23 : List CallState := ((nextList 3 wires0).drop 23).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed23 : AllRejected 7 block23 := checkedBlock (by decide +kernel)
def block24 : List CallState := ((nextList 3 wires0).drop 24).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed24 : AllRejected 7 block24 := checkedBlock (by decide +kernel)
def block25 : List CallState := ((nextList 3 wires0).drop 25).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed25 : AllRejected 7 block25 := checkedBlock (by decide +kernel)
def block26 : List CallState := ((nextList 3 wires0).drop 26).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed26 : AllRejected 7 block26 := checkedBlock (by decide +kernel)
def block27 : List CallState := ((nextList 3 wires0).drop 27).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed27 : AllRejected 7 block27 := checkedBlock (by decide +kernel)
def block28 : List CallState := ((nextList 3 wires0).drop 28).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed28 : AllRejected 7 block28 := checkedBlock (by decide +kernel)
def block29 : List CallState := ((nextList 3 wires0).drop 29).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed29 : AllRejected 7 block29 := checkedBlock (by decide +kernel)
def block30 : List CallState := ((nextList 3 wires0).drop 30).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed30 : AllRejected 7 block30 := checkedBlock (by decide +kernel)
def block31 : List CallState := ((nextList 3 wires0).drop 31).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed31 : AllRejected 7 block31 := checkedBlock (by decide +kernel)
def block32 : List CallState := ((nextList 3 wires0).drop 32).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed32 : AllRejected 7 block32 := checkedBlock (by decide +kernel)
def block33 : List CallState := ((nextList 3 wires0).drop 33).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed33 : AllRejected 7 block33 := checkedBlock (by decide +kernel)
def block34 : List CallState := ((nextList 3 wires0).drop 34).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed34 : AllRejected 7 block34 := checkedBlock (by decide +kernel)
def block35 : List CallState := ((nextList 3 wires0).drop 35).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed35 : AllRejected 7 block35 := checkedBlock (by decide +kernel)
def block36 : List CallState := ((nextList 3 wires0).drop 36).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed36 : AllRejected 7 block36 := checkedBlock (by decide +kernel)
def block37 : List CallState := ((nextList 3 wires0).drop 37).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed37 : AllRejected 7 block37 := checkedBlock (by decide +kernel)
def block38 : List CallState := ((nextList 3 wires0).drop 38).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed38 : AllRejected 7 block38 := checkedBlock (by decide +kernel)
def block39 : List CallState := ((nextList 3 wires0).drop 39).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed39 : AllRejected 7 block39 := checkedBlock (by decide +kernel)
def block40 : List CallState := ((nextList 3 wires0).drop 40).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed40 : AllRejected 7 block40 := checkedBlock (by decide +kernel)
def block41 : List CallState := ((nextList 3 wires0).drop 41).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed41 : AllRejected 7 block41 := checkedBlock (by decide +kernel)
def block42 : List CallState := ((nextList 3 wires0).drop 42).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed42 : AllRejected 7 block42 := checkedBlock (by decide +kernel)
def block43 : List CallState := ((nextList 3 wires0).drop 43).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed43 : AllRejected 7 block43 := checkedBlock (by decide +kernel)
def block44 : List CallState := ((nextList 3 wires0).drop 44).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed44 : AllRejected 7 block44 := checkedBlock (by decide +kernel)
def block45 : List CallState := ((nextList 3 wires0).drop 45).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed45 : AllRejected 7 block45 := checkedBlock (by decide +kernel)
def block46 : List CallState := ((nextList 3 wires0).drop 46).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed46 : AllRejected 7 block46 := checkedBlock (by decide +kernel)
def block47 : List CallState := ((nextList 3 wires0).drop 47).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed47 : AllRejected 7 block47 := checkedBlock (by decide +kernel)
def block48 : List CallState := ((nextList 3 wires0).drop 48).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed48 : AllRejected 7 block48 := checkedBlock (by decide +kernel)
def block49 : List CallState := ((nextList 3 wires0).drop 49).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed49 : AllRejected 7 block49 := checkedBlock (by decide +kernel)
def block50 : List CallState := ((nextList 3 wires0).drop 50).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed50 : AllRejected 7 block50 := checkedBlock (by decide +kernel)
def block51 : List CallState := ((nextList 3 wires0).drop 51).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed51 : AllRejected 7 block51 := checkedBlock (by decide +kernel)
def block52 : List CallState := ((nextList 3 wires0).drop 52).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed52 : AllRejected 7 block52 := checkedBlock (by decide +kernel)
def block53 : List CallState := ((nextList 3 wires0).drop 53).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed53 : AllRejected 7 block53 := checkedBlock (by decide +kernel)
def block54 : List CallState := ((nextList 3 wires0).drop 54).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed54 : AllRejected 7 block54 := checkedBlock (by decide +kernel)
def block55 : List CallState := ((nextList 3 wires0).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed55 : AllRejected 7 block55 := checkedBlock (by decide +kernel)
def block56 : List CallState := ((nextList 3 wires0).drop 56).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed56 : AllRejected 7 block56 := checkedBlock (by decide +kernel)
def block57 : List CallState := ((nextList 3 wires0).drop 57).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed57 : AllRejected 7 block57 := checkedBlock (by decide +kernel)
def block58 : List CallState := ((nextList 3 wires0).drop 58).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed58 : AllRejected 7 block58 := checkedBlock (by decide +kernel)
def block59 : List CallState := ((nextList 3 wires0).drop 59).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed59 : AllRejected 7 block59 := checkedBlock (by decide +kernel)
def block60 : List CallState := ((nextList 3 wires0).drop 60).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed60 : AllRejected 7 block60 := checkedBlock (by decide +kernel)
def block61 : List CallState := ((nextList 3 wires0).drop 61).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem closed61 : AllRejected 7 block61 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 24000000 in
theorem node0 : walk 8 3 wires0 = false := by
  have rest := (appendOk closed0 (appendOk closed1 (appendOk closed2 (appendOk closed3 (appendOk closed4 (appendOk closed5 (appendOk closed6 (appendOk closed7 (appendOk closed8 (appendOk closed9 (appendOk closed10 (appendOk closed11 (appendOk closed12 (appendOk closed13 (appendOk closed14 (appendOk closed15 (appendOk closed16 (appendOk closed17 (appendOk closed18 (appendOk closed19 (appendOk closed20 (appendOk closed21 (appendOk closed22 (appendOk closed23 (appendOk closed24 (appendOk closed25 (appendOk closed26 (appendOk closed27 (appendOk closed28 (appendOk closed29 (appendOk closed30 (appendOk closed31 (appendOk closed32 (appendOk closed33 (appendOk closed34 (appendOk closed35 (appendOk closed36 (appendOk closed37 (appendOk closed38 (appendOk closed39 (appendOk closed40 (appendOk closed41 (appendOk closed42 (appendOk closed43 (appendOk closed44 (appendOk closed45 (appendOk closed46 (appendOk closed47 (appendOk closed48 (appendOk closed49 (appendOk closed50 (appendOk closed51 (appendOk closed52 (appendOk closed53 (appendOk closed54 (appendOk closed55 (appendOk closed56 (appendOk closed57 (appendOk closed58 (appendOk closed59 (appendOk closed60 (appendOk closed61 (emptyOk 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 3) (ws := wires0) (by decide +kernel) (by decide +kernel) rest
end PEqualNP.Outside.L_meta_11285_aux.NatCheck.Delete2
open PEqualNP.Outside.L_meta_11285_aux in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.L_meta_11285 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fits _ computes
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have lt : binaryCost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr
      ⟨g,hm,by simp [isBinary,hn]⟩
    have sameInputs : NatCheck.asNs inputs6 = NatCheck.Delete2.wires0 := by decide +kernel
    have cert : NatCheck.walk 8 3 (NatCheck.asNs inputs6) = false := by
      rw [sameInputs]
      exact NatCheck.Delete2.node0
    have lower := ten_binary cert gs o fits computes
    exact ⟨smallCircuit.gates,smallCircuit.output,smallLegal,by change 11 ≤ gs.length; omega,smallEval⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    exact ⟨(fits g hg).1.imp_right (·.resolve_right fun h => present ⟨g,hg,h⟩), (fits g hg).2⟩
