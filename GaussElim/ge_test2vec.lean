import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1vec

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

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

def elemMat (E : ElemOp (m:=m)) := ElemOpOnMatrix I E

lemma findIdx_exists_of_lt_length (p : α → Bool) (l : List α) (h : l.findIdx p < l.length) : ∃ x∈l, p x
   := by
   have := List.findIdx_get (p:=p) (w:=h)
   use l.get ⟨List.findIdx p l, h⟩
   constructor
   · exact List.get_mem l (List.findIdx p l) h
   · exact this

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

--Finds first column of the matrix that has a nonzero entry
def findNonzCol : ℕ := (colVecofMat M).toList.findIdx (fun col => ¬ vec_allZero col)

lemma findNonzCol_le_numCol : (findNonzCol M) ≤ (colVecofMat M).length := by
  unfold findNonzCol
  simp_rw [←(colVecofMat M).toList_length]
  apply findIdx_le_length (colVecofMat M).toList (fun col => ¬vec_allZero col)

lemma nonzVecHasNonz (h : ¬vec_allZero l) : ∃ x∈l.toList, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

lemma Vector_toList_get (v : Vector α k) : ∀ i, v.get i = v.toList.get ⟨i,by simp⟩ := by intro i; rfl

lemma findNonzCol_get_HasNonz (h : findNonzCol M < (colVecofMat M).length) :
  ∃ x ∈ ((colVecofMat M).get ⟨findNonzCol M,h⟩).toList, x≠0 := by
  unfold findNonzCol at h
  simp_rw [←(colVecofMat M).toList_length] at h
  have := List.findIdx_get (w:=h)
  simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
  rw [Bool.not_iff_not] at this
  obtain ⟨x,hx,xn0⟩ := nonzVecHasNonz this
  use x
  constructor
  unfold findNonzCol
  rw [Vector_toList_get (colVecofMat M)]
  convert hx using 4
  simp only [Fin.mk]
  congr
  ext col
  simp_rw [← Bool.not_iff_not (b:=vec_allZero col)]
  simp
  assumption

def isZeroMatrix' : Bool := findNonzCol M = (colVecofMat M).length

abbrev rowsAfteri (i : Fin m) : Fin (m-i) → Fin m :=
  fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩

abbrev colsAfterj (j : Fin n) : Fin (n-j) → Fin n :=
  fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩

--Gives the block matrix starting from (i,j)th entry to (m,n)th entry
def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (rowsAfteri i) (colsAfterj j)

lemma vector_toList_get (v : Vector α k) (i : Fin k) : v.toList.get (i.cast (by simp)) = v.get i := by cases v; rfl

/- Given a mxn matrix and a point (i,j) in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the ith row and scale the pivot to 1-/
def findPivot_ij' (i : Fin m) (j : Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  let M' := botRightij M i j
  if h1 : findNonzCol M' = (colVecofMat M').length then [1]
  else
    if h2 : findNonzCol M' < (colVecofMat M').length then
      let pcol := (colVecofMat M').get ⟨findNonzCol M',h2⟩
      have h3 : pcol.toList.findIdx (fun x => x≠0) < pcol.length := by
        have h4 := findNonzCol_get_HasNonz M' h2
        unfold_let pcol
        simp_rw [← Vector.toList_length ((colVecofMat M').get ⟨findNonzCol M', h2⟩)]
        apply List.findIdx_lt_length_of_exists
        convert h4; simp
      have h3a : pcol.length = (m-i) := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol.toList < m := by
        apply lt_of_le_of_lt' _ h3; rw [h3a]; exact Nat.sub_le m ↑i
      have h3b : pcol.toList.findIdx (fun x => x≠0) < pcol.toList.length := by simp_rw [Vector.toList_length pcol]; exact h3
      have h5 : (pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩) ≠ 0 := by
        rw [← vector_toList_get pcol ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩]
        have := List.findIdx_get (w:=h3b)
        simp at this
        convert this
        simp only [Fin.coe_cast, Bool.decide_not]
      [elemMat (scalarMul (1/(pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩)) (one_div_ne_zero h5) i) ,elemMat (rowSwap i (⟨pcol.toList.findIdx (fun x => x≠0),h3'⟩+i))]
    else
      have h4 := findNonzCol_le_numCol M'
      have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
      absurd h4 nh4

def findPivot_ij (i : Fin m) (j : Fin n) : Option (List (Matrix (Fin m) (Fin m) Rat)) :=
  let M' := botRightij M i j
  if h1 : findNonzCol M' = (colVecofMat M').length then none
  else
    if h2 : findNonzCol M' < (colVecofMat M').length then
      let pcol := (colVecofMat M').get ⟨findNonzCol M',h2⟩
      have h3 : pcol.toList.findIdx (fun x => x≠0) < pcol.length := by
        have h4 := findNonzCol_get_HasNonz M' h2
        unfold_let pcol
        simp_rw [← Vector.toList_length ((colVecofMat M').get ⟨findNonzCol M', h2⟩)]
        apply List.findIdx_lt_length_of_exists
        convert h4; simp
      have h3a : pcol.length = (m-i) := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol.toList < m := by
        apply lt_of_le_of_lt' _ h3; rw [h3a]; exact Nat.sub_le m ↑i
      have h3b : pcol.toList.findIdx (fun x => x≠0) < pcol.toList.length := by simp_rw [Vector.toList_length pcol]; exact h3
      have h5 : (pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩) ≠ 0 := by
        rw [← vector_toList_get pcol ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩]
        have := List.findIdx_get (w:=h3b)
        simp at this
        convert this
        simp only [Fin.coe_cast, Bool.decide_not]
      [elemMat (scalarMul (1/(pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩)) (one_div_ne_zero h5) i), elemMat (rowSwap i (⟨pcol.toList.findIdx (fun x => x≠0),h3'⟩+i))]
    else
      have h4 := findNonzCol_le_numCol M'
      have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
      absurd h4 nh4

/-Given that the pivot is present at (i,j), it generates a list of elementary matrices that
eliminate entries in the jth column below the ith row, using the pivot-/
def elimColBelow_ij (i:Fin m) (j:Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  List.ofFn fun r : Fin (m-i-1) =>
  have h : r.val+i.val+1<m := by
    have h0 := r.2
    have h1: ↑r < m - (↑i + 1) := by simp_rw [Nat.sub_sub] at h0; exact h0
    apply Nat.add_lt_of_lt_sub h1
  elemMat (rowMulAdd (-M ⟨r+i+1,h⟩ j) ⟨r+i+1,h⟩ i)

def mat := !![0,2,3;0,5,6;0,8,(9:Rat)]

/-Row reduction algorithm - Part 1 (Row echelon form)
0. Start from (i,j) = (0,0)
1. Find pivot from (i,j) to (m,n) in matrix that has been multiplied with the operations
   upto (i,j)
2. If not found in jth col, find from (i,j+1) to (m,n)
   If found, swap - improve - eliminate, find pivot from (i+1,j+1) to (m,n)
3. End when (i,j) = (m,n)
-/

def rowEchelonStep (i : Fin m) (j : Fin n) : (Matrix (Fin m) (Fin n) Rat)×Bool :=
  match (findPivot_ij M i j) with
  | none => (M,false)
  | some listmat => ((elimColBelow_ij (listmat.prod * M) i j).prod * (listmat.prod * M),true)

def tmat := !![1,2,3;4,5,(6:Rat)]
#eval rowEchelonStep tmat 0 0
#eval rowEchelonStep (rowEchelonStep tmat 0 0).1 1 1

def tmat1 := !![1,-2,1,-1;2,1,-3,8;4,-7,1,(-2:Rat)]
#eval rowEchelonStep tmat1 0 0
-- #eval rowEchelonStep (rowEchelonStep tmat1 0 0).1 1 1
-- #eval rowEchelonStep (rowEchelonStep (rowEchelonStep tmat1 0 0) 1 1) 2 2
#eval rowEchelonStep mat 2 2

/-
1. Apply rowEchelonStep at (0,0) to M
2. If false, apply rowEchelonStep at (0,1) to M
   If true, apply rowEchelonStep at (1,1) to the matrix from the previous step
-/

def rowEchelonList_ij' (A : Matrix (Fin m) (Fin n) Rat) (i : Fin m) (j : Fin n) : (Option (List (Matrix (Fin m) (Fin m) Rat))) × (Matrix (Fin m) (Fin n) Rat) :=
  let A_step := (rowEchelonStep A i j).1
  if hi : i.val = m-1 then
    (findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j,
     ((findPivot_ij A_step ⟨m-1,Nat.sub_one_lt_of_le hm (le_refl m)⟩ j).getD []).prod * A_step)
  else
    if hj : j.val = n-1 then
      match (findPivot_ij A_step i ⟨n-1,Nat.sub_one_lt_of_le hn (le_refl n)⟩) with
      | none => (some [1],A_step)
      | some plist => (elimColBelow_ij ((List.prod plist) * A_step) i j ++ plist,(elimColBelow_ij ((List.prod plist) * A_step) i j ++ plist).prod*A_step)
    else
      have hij : i.val < m-1 ∧ j.val < n-1 := ⟨lt_of_le_of_ne (Nat.le_sub_one_of_lt i.2) hi, lt_of_le_of_ne (Nat.le_sub_one_of_lt j.2) hj⟩
      match (findPivot_ij A i j) with
      | none => (rowEchelonList_ij' A_step i ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩)
      | some l => ((rowEchelonList_ij' A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).1.getD [] ++ elimColBelow_ij ((List.prod l) * A) i j ++ l,
                    (rowEchelonList_ij' A_step ⟨i+1,Nat.add_lt_of_lt_sub hij.1⟩ ⟨j+1,Nat.add_lt_of_lt_sub hij.2⟩).2)

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

def amat := !![(1:Rat),-2,1,-1;2,1,-3,8;4,-7,1,(-2:Rat)]
#eval rowEchelonList_ij' (m:=3) (n:=4) (by linarith) (by linarith) amat 0 0
