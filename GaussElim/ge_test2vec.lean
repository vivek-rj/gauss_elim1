import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1vec

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

--Elementary matrix that multiplies ith row with scalar c
def eltScalarMul (c : Rat) (i : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i i (c-1)

--Elementary matrix that swaps ith and jth row
def eltRowSwap (i : Fin m) (j : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    let newr := (I i)
    Matrix.updateRow (Matrix.updateRow I i (I j)) j newr

--Elementary matrix that takes jth row, multiplies it with scalar c and adds it to ith row
def eltRowAdd (i : Fin m) (j : Fin m) (c : Rat) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i j c

--For a list l and proposition p, if l.findIdx p < l.length then l has an element satisfying p
lemma findIdx_exists_of_lt_length (p : α → Bool) (l : List α) (h : l.findIdx p < l.length) : ∃ x∈l, p x
   := by
   have := List.findIdx_get (p:=p) (w:=h)
   use l.get ⟨List.findIdx p l, h⟩
   constructor
   · exact List.get_mem l (List.findIdx p l) h
   · exact this

--For a list l and proposition p, if l.findIdx p = l.length then l has no element satisfying p
lemma findIdx_notExists_of_eq_length (l : List α) (p : α → Bool) (hl : l.findIdx p = l.length) : ∀ x∈l, p x = false := by
  intro x xl
  by_cases h:p x
  have := List.findIdx_lt_length_of_exists ⟨x,xl,h⟩
  have := ne_of_lt this
  contradiction
  simpa using h

--In a list l, if no element satisfies proposition p, then l.findIdx p = l.length
lemma findIdx_eq_length_of_notExists (l : List α) (p : α → Bool) (hl : ∀ x∈l, p x = false) : l.findIdx p = l.length := by
  induction' l with a as ih
  · simp
  · simp at hl; have ih' := ih hl.2
    rw [List.findIdx_cons, hl.1, cond_false]; simpa

--For a list l and proposition p, l.findIdx p ≤ l.length
lemma findIdx_le_length (l : List α) (p : α → Bool) : l.findIdx p ≤ l.length := by
  by_cases h : (∃ x∈l, p x)
  exact le_of_lt (List.findIdx_lt_length_of_exists h)
  push_neg at h; simp at h
  exact le_of_eq (findIdx_eq_length_of_notExists l p h)

--Finds first column of the matrix that has a nonzero entry
def findNonzCol : ℕ := (colVecofMat M).toList.findIdx (fun col => ¬ vec_allZero col)

--The index of the first nonzero column is less than the number of columns
lemma findNonzCol_le_numCol : (findNonzCol M) ≤ (colVecofMat M).length := by
  unfold findNonzCol
  simp_rw [←(colVecofMat M).toList_length]
  apply findIdx_le_length (colVecofMat M).toList (fun col => ¬vec_allZero col)

#check 1 ∈ [0,1,2,3]
#check (⟨[0,1,2,3],rfl⟩ : Vector Rat 4)

lemma nonzListHasNonz (h : ¬vec_allZero l) : ∃ x∈l.toList, x≠0 := by
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
  obtain ⟨x,hx,xn0⟩ := nonzListHasNonz this
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

--Checks whether all entries of a matrix are zero
def isZeroMatrix' : Bool := findNonzCol M = (colVecofMat M).length

abbrev rowsAfteri (i : Fin m) : Fin (m-i) → Fin m :=
  fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩

abbrev colsAfterj (j : Fin n) : Fin (n-j) → Fin n :=
  fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩

--Gives the block matrix starting from (i,j)th entry to (m,n)th entry
def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (rowsAfteri i) (colsAfterj j)

/- Given a mxn matrix and a point (i,j) in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the ith row and scale the pivot to 1-/
def findPivot_ij (i : Fin m) (j : Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
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
      --have h2' : findNonzCol M' < n := by simp_rw [←colListLength_eq_numCol M]; apply lt_of_le_of_lt' _ h2; simp
      have h3a : pcol.length = (m-i) := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol.toList < m := by
        apply lt_of_le_of_lt' _ h3; rw [h3a]; exact Nat.sub_le m ↑i
      [eltScalarMul (1/(pcol.get ⟨pcol.toList.findIdx (fun x => x≠0),h3⟩)) i ,eltRowSwap i (⟨pcol.toList.findIdx (fun x => x≠0),h3'⟩+i)]
      --(pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩,⟨pcol.findIdx (fun x => x≠0),h3'⟩+i,⟨findNonzCol M',h2'⟩+j)
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
  eltRowAdd ⟨r+i+1,h⟩ i (-M ⟨r+i+1,h⟩ j)

--!![1,2,3;4,5,6;7,8,9]
#eval elimColBelow_ij !![1,2,3;4,1,6;7,8,9] 2 2
