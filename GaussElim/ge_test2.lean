import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m>0) (hn : n>0)

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

def eltScalarMul (c : Rat) (i : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i i (c-1)

def eltRowSwap (i : Fin m) (j : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    let newr := (I i)
    Matrix.updateRow (Matrix.updateRow I i (I j)) j newr

def eltRowAdd (i : Fin m) (j : Fin m) (c : Rat) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i j c

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

def findNonzCol : ℕ := (colListofMat M).findIdx (fun col => ¬ list_allZero col)

lemma findNonzCol_le_numCol : (findNonzCol M) ≤ (colListofMat M).length := by
  unfold findNonzCol
  apply findIdx_le_length (colListofMat M) (fun col => ¬list_allZero col)

lemma nonzListHasNonz (h : ¬list_allZero l) : ∃ x∈l, x≠0 := by
  rw [List.all_eq_true] at h
  push_neg at h
  convert h; simp

lemma findNonzCol_get_HasNonz (h : findNonzCol M < (colListofMat M).length) :
  ∃ x ∈ (colListofMat M).get ⟨findNonzCol M,h⟩, x≠0 := by
  unfold findNonzCol at h
  have := List.findIdx_get (w:=h)
  simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
  rw [Bool.not_iff_not] at this
  obtain ⟨x,hx,xn0⟩ := nonzListHasNonz this
  use x
  constructor
  unfold findNonzCol
  convert hx using 4; ext col
  simp_rw [←Bool.not_iff_not (b:=list_allZero col)]
  simp
  assumption

def isZeroMatrix' : Bool := findNonzCol M = (colListofMat M).length

abbrev rowsAfteri (i : Fin m) : Fin (m-i) → Fin m :=
  fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩

abbrev colsAfterj (j : Fin n) : Fin (n-j) → Fin n :=
  fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩

def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (rowsAfteri i) (colsAfterj j)

/- Given a mxn matrix and a point (i,j) in it, it will find the pivot column and return
elementary matrices that swap the pivot row with the ith row and scale the pivot to 1-/
def findPivot_ij (i : Fin m) (j : Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  let M' := botRightij M i j
  if h1 : findNonzCol M' = (colListofMat M').length then [1]
  else
    if h2 : findNonzCol M' < (colListofMat M').length then
      let pcol := (colListofMat M').get ⟨findNonzCol M',h2⟩
      have h3 : pcol.findIdx (fun x => x≠0) < pcol.length := by
        have h4 := findNonzCol_get_HasNonz M' h2
        unfold_let pcol
        apply List.findIdx_lt_length_of_exists
        convert h4; simp
      --have h2' : findNonzCol M' < n := by simp_rw [←colListLength_eq_numCol M]; apply lt_of_le_of_lt' _ h2; simp
      have h3a : pcol.length = (m-i) := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol < m := by
        apply lt_of_le_of_lt' _ h3; rw [h3a]; exact Nat.sub_le m ↑i
      [eltScalarMul (1/(pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩)) i ,eltRowSwap i (⟨pcol.findIdx (fun x => x≠0),h3'⟩+i)]
      --(pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩,⟨pcol.findIdx (fun x => x≠0),h3'⟩+i,⟨findNonzCol M',h2'⟩+j)
    else
      have h4 := findNonzCol_le_numCol M'
      have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
      absurd h4 nh4

#eval findPivot_ij !![6,0,3;0,5,6;0,8,9]
#eval eltRowSwap (m:=3)
#check Nat.sub_lt_iff_lt_add

example (j:Fin m) : m - j.val ≤ m := by exact Nat.sub_le m ↑j

def elimColBelow_ij (i:Fin m) (j:Fin n) : List (Matrix (Fin m) (Fin m) Rat) :=
  -- List.ofFn fun r : Fin (m-i-1) => eltRowAdd ⟨r+1,lt_of_le_of_lt' (Nat.sub_le m i.val) (Nat.add_lt_of_lt_sub r.2 (b:=1))⟩ i (-M ⟨r+1,lt_of_le_of_lt' (Nat.sub_le m ↑i) (Nat.add_lt_of_lt_sub r.2 (b:=1))⟩ j)
  List.ofFn fun r : Fin (m-i-1) =>
  have h : r.val+i.val+1<m := by
    have h0 := r.2
    have h1: ↑r < m - (↑i + 1) := by simp_rw [Nat.sub_sub] at h0; exact h0
    apply Nat.add_lt_of_lt_sub h1
  eltRowAdd ⟨r+i+1,h⟩ i (-M ⟨r+i+1,h⟩ j)

--by ; ; exact h0; apply Nat.sub_lt_
--; have:↑r + 1 < m := lt_of_le_of_lt' _ this;
--!![1,2,3;4,5,6;7,8,9]
#eval elimColBelow_ij !![1,2,3;4,1,6;7,8,9] 2 2
