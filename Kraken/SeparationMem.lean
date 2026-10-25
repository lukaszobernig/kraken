module

import Kraken.Attribute
public import Kraken.Mem
import all Kraken.Mem
public import Kraken.OmniSemantics
public import Kraken.Separation
import all Kraken.Separation
public meta import Lean.Elab.SyntheticMVars

public section

/-!
# Separation-logic interface to Kraken memory-access operations
-/

open Std
open Std.ExtHashMap
open List

syntax:62 (name := memAtStx) term:63 " @ " term:63 : term

@[term_elab memAtStx]
meta def elabMemAt : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let v : Lean.TSyntax `term := ⟨stx[0]⟩
  let a : Lean.TSyntax `term := ⟨stx[2]⟩
  let aExpr ← Lean.Elab.Term.elabTermAndSynthesize a none
  let aType ← Lean.Meta.whnf (← Lean.Meta.inferType aExpr)
  let addrStx ←
    if aType.isConstOf ``UInt64 then
      `($(← Lean.Elab.Term.exprToSyntax aExpr).toBitVec)
    else
      Lean.Elab.Term.exprToSyntax aExpr
  Lean.Elab.Term.elabTerm (← `(Eq (($v).At $addrStx))) expectedType?

private theorem Std.ExtHashMap.get_union_l_disjoint {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 : ExtHashMap key value) (k : key) (v : value) (h_disj : m1.inter m2 = ∅) (h : m1.get? k = some v) :
    (m1.union m2).get? k = some v := by
  rw [get?_eq_getElem?] at h
  rw [get?_eq_getElem?, union_comm_of_disjoint m1 m2 h_disj]
  simp only [union_eq, getElem?_union, h, Option.some_or]

private theorem Std.ExtHashMap.union_union_override {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 m3 : ExtHashMap key value) (h_sub : ∀ k, k ∈ m1 → k ∈ m3) :
    (m1.union m2).union m3 = m2.union m3 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union]
  cases h3 : m3[k]?
  · have h_not_mem3 : ¬ k ∈ m3 := by
      intro h_mem
      have h_some := getElem?_eq_some_getElem h_mem
      rw [h3] at h_some
      contradiction
    have h_not_mem1 : ¬ k ∈ m1 := fun h => h_not_mem3 (h_sub k h)
    have h1 := getElem?_eq_none h_not_mem1
    rw [h1]
    cases h2 : m2[k]?
    · rfl
    · rfl
  · rfl

private theorem List.mapM_loop_id_some {α : Type} (xs : List α) (acc : List α) :
    List.mapM.loop id (xs.map some) acc = some (acc.reverse ++ xs) := by
  induction xs generalizing acc <;> simp_all [List.mapM.loop]

private theorem List.allSome_map_some {α : Type} (l : List α) : List.allSome (l.map some) = some l := by
  exact List.mapM_loop_id_some l []

private theorem List.range_get_eq_map_some {α : Type} (l : List α) :
    (List.range l.length).map (fun i => if h : i < l.length then some (l.get ⟨i, h⟩) else none) = l.map some := by
  apply List.ext_get <;> simp

private theorem mem_At_samerange {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (h_len : _bs.length = bs.length) (k : BitVec w) :
    (k ∈ bs.At a) = (k ∈ _bs.At a) := by
  exact propext (by simp [mem_At_iff, h_len])

private theorem disjoint_Atsame_l_same_r {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (m2 : Mem w)
    (h_disj : (_bs.At a).inter m2 = ∅) (h_len : _bs.length = bs.length) :
    (bs.At a).inter m2 = ∅ := by
  simpa [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff,
    mem_At_samerange _bs bs a h_len] using h_disj

namespace Mem

theorem loadBytes_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadBytes a n = some bs := by
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  rw [← h_union]
  have h_get : ∀ i (h : i < n), ((bs.At a).union m2).get? (a + BitVec.ofNat w i) = some (bs.get ⟨i, Hl ▸ h⟩) := by
    intro i hi
    apply get_union_l_disjoint
    · exact h_inter
    · rw [get?_At_idx _ _ _ (by omega) (Hl.symm ▸ Hlw)]
      exact getElem?_eq_getElem (Hl ▸ hi)
  rw [Mem.loadBytes]
  rw [show (List.range n).map (fun i => ((bs.At a).union m2).get? (a + BitVec.ofNat w i)) =
           (List.range n).map (fun i => if h : i < n then some (bs.get ⟨i, Hl ▸ h⟩) else none) by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; simp only [hi, ↓reduceDIte]; exact h_get i hi]
  cases Hl
  rw [List.range_get_eq_map_some]
  rw [List.allSome_map_some]

theorem storeBytes_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n ∧ bs.length = n) :
    (m.storeBytes a bs) =⋆ Eq (bs.At a) ⋆ R := by
  have ⟨Hsep, h_len1, h_len2⟩ := H
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  dsimp [storeBytes]
  rw [← h_union]
  rw [union_union_override (_bs.At a) m2 (bs.At a) (by
    intro k hk; rw [mem_At_samerange _bs bs a (by omega)]; exact hk)]
  rw [sep_comm]
  exact ⟨m2, bs.At a, rfl, disjoint_symm (disjoint_Atsame_l_same_r _bs bs a m2 h_inter (by omega)), hR, rfl⟩

theorem loadInt_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  simp [loadInt, loadBytes_sep bs a n R m Hsep Hl Hlw]

theorem storeInt_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ Eq ((Int.toBytes n v).At a) ⋆ R := by
  simpa only [storeInt] using
    storeBytes_sep a n _bs (Int.toBytes n v) R m ⟨H.1, H.2, Int.toBytes_length n v⟩

theorem At_append_sep {w : Nat} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    Eq ((bs1 ++ bs2).At a) = Eq (bs1.At a) ⋆ Eq (bs2.At (a + .ofNat _ bs1.length)) := by
  funext m
  apply propext
  constructor
  · rintro rfl
    rw [List.At_append _ _ _ h_len]
    exact ⟨bs1.At a, bs2.At (a + BitVec.ofNat w bs1.length), rfl, List.disjoint_At_append _ _ _ h_len, rfl, rfl⟩
  · rintro ⟨m1, m2, h_union, h_disj, rfl, rfl⟩
    rw [← h_union]
    rw [← List.At_append _ _ _ h_len]

theorem At_take_drop_sep {w : Nat} (bs : List UInt8) (n : Nat) (a : BitVec w)
    (h_n : n ≤ bs.length) (h_len : bs.length ≤ 2 ^ w) :
    Eq (bs.At a) = Eq ((bs.take n).At a) ⋆ Eq ((bs.drop n).At (a + BitVec.ofNat w n)) := by
  have h_app : bs.take n ++ bs.drop n = bs := List.take_append_drop n bs
  have h_len' : (bs.take n).length + (bs.drop n).length ≤ 2 ^ w := by
    have := congrArg List.length h_app
    rw [List.length_append] at this
    omega
  have h_take_len : (bs.take n).length = n := List.length_take_of_le h_n
  conv => lhs; rw [← h_app]
  rw [At_append_sep (bs.take n) (bs.drop n) a h_len', h_take_len]

@[simp]
theorem At_nil_sep {w : Nat} (a : BitVec w) :
    Eq (([] : List UInt8).At a) = emp := by
  funext m
  simp [List.At, emp, eq_comm]

theorem At_slice_sep {w : Nat} (bs : List UInt8) (off k : Nat) (a : BitVec w)
    (h_slice : off + k ≤ bs.length) (h_len : bs.length ≤ 2 ^ w) :
    Eq (bs.At a) =
      Eq ((bs.take off).At a) ⋆
      (Eq (((bs.drop off).take k).At (a + BitVec.ofNat w off)) ⋆
       Eq ((bs.drop (off + k)).At (a + BitVec.ofNat w (off + k)))) := by
  rw [At_take_drop_sep bs off a (by omega) h_len]
  rw [At_take_drop_sep (bs.drop off) k (a + BitVec.ofNat w off) (by simp; omega) (by simp; omega)]
  have h_drop : (bs.drop off).drop k = bs.drop (off + k) := by
    rw [List.drop_drop, Nat.add_comm]
  have h_add : a + BitVec.ofNat w off + BitVec.ofNat w k = a + BitVec.ofNat w (off + k) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h_drop, h_add]

end Mem

theorem store_sep {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) (w : Width) (v : w.type)
    (ret : MD → Kraken.Effects MD)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : HasDataMem.dmem s =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeInt (HasDataMem.dmem s) addr w.bytes v.toInt
    MachineData.store s addr v ret =
      require_write_access addr w (fun _ =>
        ret (HasDataMem.withDmem s mem')) := by
  have h_load : Mem.loadInt (HasDataMem.dmem s) addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R (HasDataMem.dmem s) h_mem h_len (by cases w <;> decide)
  simp only [MachineData.store, h_load]

theorem load_sep {MD : Type} [HasDataMem MD]
    (s : MD) (addr : BitVec 64) (w : Width)
    (ret : w.type → MD → Kraken.Effects MD)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : HasDataMem.dmem s =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_read_access addr w (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.load,
    Mem.loadInt_sep bs addr w.bytes R (HasDataMem.dmem s) h_mem h_len (by cases w <;> decide)]

@[kspec]
theorem Kraken.Effects.All_store_sep {MD : Type} [HasDataMem MD]
    (post : TracedPost MD) (s : MD) (addr addr' : BitVec 64)
    (w : Width) (v : w.type) (ret : MD → Kraken.Effects MD)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : HasDataMem.dmem s =⋆ Eq (bs.At addr') ⋆ R)
    (h_addr : addr = addr')
    (h_len : bs.length = w.bytes) :
    (MachineData.store s addr v ret).All post =
      let mem' := Mem.storeInt (HasDataMem.dmem s) addr' w.bytes v.toInt
      ((mem' =⋆ Eq ((Int.toBytes w.bytes v.toInt).At addr') ⋆ R) →
        (ret (HasDataMem.withDmem s mem')).All (fun a tr => post a (.write addr' w :: tr))) := by
  subst h_addr
  have h_load : Mem.loadInt (HasDataMem.dmem s) addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R (HasDataMem.dmem s) h_mem h_len (by cases w <;> decide)
  have h_store : Mem.storeInt (HasDataMem.dmem s) addr w.bytes v.toInt =⋆ Eq ((Int.toBytes w.bytes v.toInt).At addr) ⋆ R :=
    Mem.storeInt_sep addr w.bytes bs R (HasDataMem.dmem s) ⟨h_mem, h_len⟩ v.toInt
  exact propext ⟨fun h _ => by simpa [MachineData.store, h_load, Kraken.Effects.All] using h,
    fun h => by simpa [MachineData.store, h_load, Kraken.Effects.All] using h h_store⟩

@[kspec]
theorem Kraken.Effects.All_load_sep {MD : Type} [HasDataMem MD]
    (post : TracedPost MD) (s : MD) (addr addr' : BitVec 64)
    (w : Width) (ret : w.type → MD → Kraken.Effects MD)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : HasDataMem.dmem s =⋆ Eq (bs.At addr') ⋆ R)
    (h_addr : addr = addr')
    (h_len : bs.length = w.bytes) :
    (MachineData.load s addr w ret).All post =
      (ret (.ofInt w.bits (Int.ofBytes bs)) s).All (fun a tr => post a (.read addr' w :: tr)) := by
  subst h_addr
  have h_load : Mem.loadInt (HasDataMem.dmem s) addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R (HasDataMem.dmem s) h_mem h_len (by cases w <;> decide)
  simp only [MachineData.load, h_load, Kraken.Effects.All]
