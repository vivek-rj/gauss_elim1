import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1vec

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

inductive ElemOp : Type where
| scalarMul (c : Rat) (hc : c≠0) (i : Fin m) : ElemOp
| rowSwap (i : Fin m) (j : Fin m) : ElemOp
| rowMulAdd (c : Rat) (i : Fin m) (j : Fin m) : ElemOp
--deriving Repr

namespace ElemOp

def ElemOpOnMatrix (E : ElemOp (m:=m)) : Matrix (Fin m) (Fin n) Rat :=
match E with
| scalarMul c _ i => M.updateRow i (c • (M i))
| rowSwap i j => let newr := (M i)
    Matrix.updateRow (Matrix.updateRow M i (M j)) j newr
| rowMulAdd c i j => M.updateRow i (M i + (c • (M j)))

def elemMat (E : ElemOp (m:=m)) := ElemOpOnMatrix (Matrix.diagonal (fun _:Fin m => (1:Rat))) E

lemma findIdx_notExists_of_eq_length (l : List α) (p : α → Bool) (hl : l.findIdx p = l.length) : ∀ x∈l, p x = false := by
  intro x xl
  by_cases h:p x
  have := List.findIdx_lt_length_of_exists ⟨x,xl,h⟩
  have := ne_of_lt this
  contradiction
  simpa using h

lemma findIdx_eq_length_of_notExists (l : List α) (p : α → Bool) (hl : ∀ x∈l, p x = false) : l.findIdx p = l.length := by
  induction' l with a as ih
  · simp
  · simp at hl; have ih' := ih hl.2
    rw [List.findIdx_cons, hl.1, cond_false]; simpa

lemma findIdx_le_length (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length := by
  by_cases h : (∃ x∈l, p x)
  exact le_of_lt (List.findIdx_lt_length_of_exists h)
  push_neg at h; simp at h
  exact le_of_eq (findIdx_eq_length_of_notExists l p h)

--define general inductive function on vectors that finds 1st elt satisfying p, gives its index (Option Fin)
-- and proof that it satisfies p and all elements before it dont satisfy p

--Finds first column of the matrix that has a nonzero entry

lemma nonzVecHasNonz (h : ¬vec_allZero l) : ∃ x∈l.toList, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

lemma nonzListHasNonz (h : ¬list_allZero l) : ∃ x∈l, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

def indNonzCol : Option {idx : Fin n // ∃ x ∈ ((colVecofMat M).get idx).toList,x ≠ 0} :=
  (colVecofMat M).inductionOn
  (none)
  (fun _ {x} => fun
  | none => if h:vec_allZero x then none else some ⟨0,nonzVecHasNonz h⟩
  | some ⟨idx,h'⟩ => if h:vec_allZero x then some ⟨(idx.succ.cast (by simp)),by simp [h']⟩ else some ⟨0,nonzVecHasNonz h⟩)

lemma vector_toList_get (v : Vector α k) : ∀ i, v.get i = v.toList.get ⟨i,by simp⟩ := by intro i; rfl

-- def isZeroMatrix' : Bool := indNonzCol M = (colVecofMat M).length

--Gives the block matrix starting from (i,j)th entry to (m,n)th entry
def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩) (fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩)

/- Given a mxn matrix and a point (i,j) in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the ith row and scale the pivot to 1-/

def indNonzElt (v : Vector Rat k) : Option {idx : Fin k // v.get idx ≠ 0} :=
  v.inductionOn
  (none)
  (fun _ {x} => fun
  | none => if h:x=0 then none else some ⟨0,by simp [h]⟩
  | some idx => if h:x=0 then some ⟨idx.1.succ.cast (by simp),by simp [idx.2]⟩ else some ⟨0,by simp [h]⟩)

lemma indNonzElt_some_ex (v : Vector Rat k) (h : ∃ x ∈ v.toList, x≠0) : (indNonzElt v).isSome = true := by
  -- induction' hl:v.toList with a as ih
  -- · rw [hl] at h; simp at h
  -- · rw [hl] at h; simp at h
  --   rcases h with h|h
  -- induction' v with l lenl
  -- induction' l with a as ih
  -- · simp at h
  -- · simp at h
  --   rcases h with h|h
  --   unfold indNonzElt;
  sorry

#check Fin.cast

def findPivot_ij (i : Fin m) (j : Fin n) : Option (List (Matrix (Fin m) (Fin m) Rat)) :=
  let M' := botRightij M i j
  match indNonzCol M' with
  | none => none
  | some idx =>
      let pcol := (colVecofMat M').get idx
      let pivIdx := (indNonzElt pcol).get (indNonzElt_some_ex pcol idx.2)
      -- have h1 : pivIdx < pcol.length := by
      --   unfold_let pcol
      --   simp_rw [← Vector.toList_length ((colVecofMat M').get idx)]
      --   apply List.findIdx_lt_length_of_exists
      --   convert idx.2; simp
      -- have h2 : pcol.get ⟨List.findIdx (fun x ↦ decide (x ≠ 0)) pcol.toList, h1⟩ ≠ 0 := by
      --   rw [vector_toList_get pcol ⟨pcol.toList.findIdx (fun x => x≠0),h1⟩]
      --   have h2' : pcol.toList.findIdx (fun x => x≠0) < pcol.toList.length := by simp_rw [Vector.toList_length pcol]; exact h1
      --   have := List.findIdx_get (w:=h2')
      --   simp at this
      --   convert this
      --   simp only [Fin.coe_cast, Bool.decide_not]
      some [elemMat (scalarMul (1/pcol.get (pivIdx)) (one_div_ne_zero pivIdx.2) i), elemMat (rowSwap i ((pivIdx.1.castLT (Fin.val_lt_of_le ↑pivIdx.1 (Nat.sub_le m ↑i))) +i))]

def mat := !![0,2,3;4,5,6;7,8,(9:Rat)]
#eval findPivot_ij mat 0 0

--Define recursively over list of columns of matrix
def findPivot_ij' (i : Fin m) (j : Fin n) : Option (List (Matrix (Fin m) (Fin m) Rat)) :=
  let M' := botRightij M i j
  if h1 : indNonzCol M' = (colVecofMat M').length then none
  else
    have h2 := lt_of_le_of_ne (indNonzCol_le_numCol M') h1
    let pcol := (colVecofMat M').get ⟨indNonzCol M',h2⟩
    have h3 : pcol.toList.findIdx (fun x => x≠0) < pcol.length := by
      have h4 := indNonzCol_get_HasNonz M' h2
      unfold_let pcol
      simp_rw [← Vector.toList_length ((colVecofMat M').get ⟨indNonzCol M', h2⟩)]
      apply List.findIdx_lt_length_of_exists
      convert h4; simp
    have h3a : pcol.length = (m-i) := by unfold_let pcol; simp
    have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol.toList < m := by
      apply lt_of_le_of_lt' _ h3; rw [h3a]; exact Nat.sub_le m ↑i
    have h3b : pcol.toList.findIdx (fun x => x≠0) < pcol.toList.length := by simp_rw [Vector.toList_length pcol]; exact h3
    have h5 : (pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩) ≠ 0 := by
      rw [vector_toList_get pcol ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩]
      have := List.findIdx_get (w:=h3b)
      simp at this
      convert this
      simp only [Fin.coe_cast, Bool.decide_not]
    [elemMat (scalarMul (1/(pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩)) (one_div_ne_zero h5) i), elemMat (rowSwap i (⟨pcol.toList.findIdx (fun x => x≠0),h3'⟩+i))]

def findPivot_ij'' (i : Fin m) (j : Fin n) : List ElemOp :=
  (colVecofMat (botRightij M i j)).inductionOn
  ([])
  (match )

/-Given that the pivot is present at (i,j), it generates a list of elementary matrices that
eliminate entries in the jth column below the ith row, using the pivot-/
def elimColBelow_ij (i:Fin m) (j:Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  List.ofFn fun r : Fin (m-i-1) =>
  have h : r.val+(i.val+1)<m := (Nat.add_lt_of_lt_sub (Eq.subst (Nat.sub_sub m i.1 1) (r.2)))
  elemMat (rowMulAdd (-M ⟨r+i+1,h⟩ j) ⟨r+i+1,h⟩ i)

/-Row reduction algorithm - Part 1 (Row echelon form)
0. Start from (i,j) = (0,0)
1. Find pivot from (i,j) to (m,n) in matrix that has been multiplied with the operations
   upto (i,j)
2. If not found in jth col, find from (i,j+1) to (m,n)
   If found, swap - improve - eliminate, find pivot from (i+1,j+1) to (m,n)
3. End when (i,j) = (m,n)
-/

def rowEchelonStep (i : Fin m) (j : Fin n) : (Matrix (Fin m) (Fin n) Rat) :=
  match (findPivot_ij M i j) with
  | none => M
  | some listmat => (elimColBelow_ij (listmat.prod * M) i j).prod * (listmat.prod * M)

def rowEchelonList (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) (j : Fin n) : (Option (List (Matrix (Fin m) (Fin m) Rat))) × (Matrix (Fin m) (Fin n) Rat) :=
  let A_step := rowEchelonStep A i j
  if hi : i.val = m-1 then
    (findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j,
     ((findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j).getD []).prod * A_step)
  else
    if hj : j.val = n-1 then
      match (findPivot_ij A_step i ⟨n-1,Nat.sub_one_lt_of_le hn (le_refl n)⟩) with
      | none => (some [],A_step)
      | some plist => (elimColBelow_ij ((List.prod plist) * A_step) i j ++ plist,(elimColBelow_ij ((List.prod plist) * A_step) i j ++ plist).prod*A_step)
    else
      have hij : i.val < m-1 ∧ j.val < n-1 := ⟨lt_of_le_of_ne (Nat.le_sub_one_of_lt i.2) hi, lt_of_le_of_ne (Nat.le_sub_one_of_lt j.2) hj⟩
      match (findPivot_ij A i j) with
      | none => (rowEchelonList A_step i ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩)
      | some l => ((rowEchelonList A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).1.getD [] ++ elimColBelow_ij ((List.prod l) * A) i j ++ l,
                    (rowEchelonList A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).2)

  termination_by (m-i.val,n-j.val)
  decreasing_by
  · simp_wf
    right
    have hj1 : j.val+1 < n := by apply Nat.add_lt_of_lt_sub hij.2
    apply lt_of_tsub_lt_tsub_left (a:=n); rw [Nat.sub_sub_self (le_of_lt j.2), Nat.sub_sub_self (le_of_lt hj1)]; linarith
  · simp_wf
    left
    have hi1 : i.val+1 < m := by apply Nat.add_lt_of_lt_sub hij.1
    apply lt_of_tsub_lt_tsub_left (a:=m); rw [Nat.sub_sub_self (le_of_lt i.2), Nat.sub_sub_self (le_of_lt hi1)]; linarith

def elimColAbove_ij (i : Fin m) (j : Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  List.ofFn fun r : Fin i => elemMat (rowMulAdd (-M ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ j) ⟨r,Fin.val_lt_of_le r (le_of_lt i.2)⟩ i)

/-Back substitution:
Start from the bottommost row
Find index of 1
Eliminate column above-/

--make inductive defn if hard to prove
def backSubstitution (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) : (List (Matrix (Fin m) (Fin m) Rat)) :=
  if h' : i = ⟨0,hm⟩ then [] else
    if h : vec_allZero (Vector.ofFn (A i)) then backSubstitution A ⟨i-1,tsub_lt_of_lt i.2⟩ else
      have hl := List.findIdx_lt_length_of_exists (p:=fun x => x≠0) (xs:=(Vector.ofFn (A i)).toList) (by convert nonzVecHasNonz h; simp)
      let listmat := elimColAbove_ij A i ⟨(Vector.ofFn (A i)).toList.findIdx (fun x => x≠0),by convert hl; simp⟩
      (backSubstitution A ⟨i-1,tsub_lt_of_lt i.2⟩) ++ listmat

  termination_by i
  decreasing_by all_goals
  simp_wf
  apply Fin.val_fin_lt.mp; simp
  have : i.val ≠ 0 := by
    convert h'
    constructor
    · exact Fin.eq_mk_iff_val_eq.mpr
    · intro p; exact False.elim (h' p)
  apply Nat.sub_one_lt_of_le (by apply lt_of_le_of_ne (Nat.zero_le i.val) (Ne.symm this)) (le_refl i.val)

#eval backSubstitution (by linarith) !![1,-2,1,-1;0,1,-3,2;0,0,1,0]

def rowReducedEchelonForm : List (Matrix (Fin m) (Fin m) Rat) × Matrix (Fin m) (Fin n) Rat :=
  let (l1,M') := rowEchelonList hm hn M ⟨0,hm⟩ ⟨0,hn⟩
  let l2 := backSubstitution hm M' ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩
  (l2++l1.getD [],l2.prod*M')

-- count_heartbeats in
-- #eval rowReducedEchelonForm  !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)

#eval rowReducedEchelonForm  !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith)
