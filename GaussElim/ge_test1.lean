import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import GaussElim.ReducedEchelon1

variable (M : Matrix (Fin m) (Fin n) Rat) (hm : m > 0) (hn : n > 0)

def I : Matrix (Fin m) (Fin m) Rat := Matrix.diagonal (fun _ => (1:Rat))

def eltScalarMul (c : Rat) (i : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i i (c-1)

def eltRowSwap (i : Fin m) (j : Fin m) : Matrix (Fin m) (Fin m) Rat :=
    let newr := (I i)
    Matrix.updateRow (Matrix.updateRow I i (I j)) j newr

def eltRowAdd (i : Fin m) (j : Fin m) (c : Rat) : Matrix (Fin m) (Fin m) Rat :=
    1 + Matrix.stdBasisMatrix i j c

example (x : Rat) (l : List Rat) (k : l.indexOf x < l.length) : x ∈ l := by
  exact List.indexOf_lt_length.mp k

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

-- lemma nonzInRowList_imp_nonzInColList : (∃ r ∈ rowListofMat M, ¬list_allZero r) ↔
--   ∃ c ∈ colListofMat M, ¬list_allZero c := by
--   sorry
  -- constructor
  -- intro h
  -- rcases h with ⟨row,row_rl,hrow⟩
  -- rw [List.all_eq_true] at hrow; push_neg at hrow
  -- rcases hrow with ⟨x,xrow,xn0⟩
  -- have : List.indexOf x row < (colListofMat M).length := by
  --   rw [colListLength_eq_numCol]
  --   have := List.indexOf_lt_length.mpr row_rl
  --   rw [←rowListofMat_elt_length_eq_numCol M ⟨(rowListofMat M).indexOf row,by convert this⟩]
  -- let col := (colListofMat M).get ⟨row.indexOf x,_⟩

-- lemma isZeroMatrix_eq : isZeroMatrix M = isZeroMatrix' M := by
--   by_cases h : isZeroMatrix' M
--   · unfold isZeroMatrix; rw [h,List.all_eq_true]
--     unfold isZeroMatrix' at h; simp only [decide_eq_true_eq] at h
--     contrapose h; push_neg at *
--     have := (nonzInRowList_imp_nonzInColList M).mp h
--     unfold findNonzCol
--     apply ne_of_lt
--     apply List.findIdx_lt_length_of_exists
--     convert this; simp
--   · simp at h; unfold isZeroMatrix; rw [h]; unfold isZeroMatrix' at h
--     unfold findNonzCol at h
--     simp only [decide_eq_false_iff_not] at h
--     sorry
    -- contrapose h; push_neg at *; simp; unfold findNonzCol
    -- simp_rw [←colListLength_eq_numCol M]
    -- apply findIdx_eq_length_of_notExists
    -- have : ∀ col ∈ (colListofMat M), list_allZero col := by
      -- intro col hcol
      -- simp
      -- intro x xcol
    --   let i := Fin.mk (col.indexOf x) (List.indexOf_lt_length.mpr xcol)
    --   let j := Fin.mk ((colListofMat M).indexOf col) (by convert List.indexOf_lt_length.mpr hcol)
    --   have hi : col.length = m := colListofMat_elt_length_eq_numRow' M col hcol
    --   let i' := Fin.cast (hi) i
    --   let j' := Fin.cast (colListLength_eq_numCol M) j
    --   have zero_elt := h i' j'
    --   have : M i' j' = x := by
    --     unfold_let i' i j' j
    --     simp only [Fin.cast_mk]
    --     rw [rowList_get M ⟨List.indexOf x col,List.indexOf_lt_length.mpr xcol⟩]

  -- · unfold isZeroMatrix; rw [h,List.all_eq_true]
  --   intro x xrl
  --   unfold isZeroMatrix' at h; simp only [decide_eq_true_eq] at h
  --   have h := findIdx_notExists_of_eq_length _ _ h; simp at h


-- Returns value of pivot and its location
def findPivot : (Option Rat)×(Fin m)×(Fin n) :=
  if h1 : findNonzCol M = (colListofMat M).length then (none,⟨0,hm⟩,⟨0,hn⟩)
  else
    if h2 : findNonzCol M < (colListofMat M).length then
      let pcol := (colListofMat M).get ⟨findNonzCol M,h2⟩
      have h3 : pcol.findIdx (fun x => x≠0) < pcol.length := by
        have h4 := findNonzCol_get_HasNonz M h2
        unfold_let pcol
        apply List.findIdx_lt_length_of_exists
        convert h4; simp
      have h2' : findNonzCol M < n := by simp_rw [←colListLength_eq_numCol M]; assumption
      have h3a : pcol.length = m := by unfold_let pcol; simp
      have h3' : List.findIdx (fun x => decide (x ≠ 0)) pcol < m := by
        rw [← h3a]; exact h3
      (pcol.get ⟨pcol.findIdx (fun x => x≠0),h3⟩,⟨pcol.findIdx (fun x => x≠0),h3'⟩,⟨findNonzCol M,h2'⟩)
    else
      have h4 := findNonzCol_le_numCol M
      have nh4 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1))
      absurd h4 nh4

abbrev rowsAfteri (i : Fin m) : Fin (m-i) → Fin m :=
  fun k => ⟨k+i,Nat.add_lt_of_lt_sub k.2⟩

abbrev colsAfterj (j : Fin n) : Fin (n-j) → Fin n :=
  fun l => ⟨l+j,Nat.add_lt_of_lt_sub l.2⟩

def botRightij (i : Fin m) (j : Fin n) : Matrix (Fin (m-i)) (Fin (n-j)) Rat :=
  M.submatrix (rowsAfteri i) (colsAfterj j)

#eval botRightij !![1,2,3;4,5,6;7,8,9] 1 1
#eval botRightij !![1,2,3,6;2,-3,2,14;3,1,-1,2] 2 3
#check List.get

def listFind (l : List α) (p : α → Bool) (h : ∃ x ∈ l, p x) : α×(Fin (l.length)) :=
  (l.get ⟨l.findIdx p,List.findIdx_lt_length_of_exists h⟩,⟨l.findIdx p,List.findIdx_lt_length_of_exists h⟩)

#eval listFind [0,1,2,3] (fun x => x≥2) (by use 3;simp)
#check Prod.Lex
#check List.pmap

def findPivot_ij (i : Fin m) (j : Fin n) : (Option Rat)×(Fin m)×(Fin n) :=
  match h : (i.val,j.val) with
  | (0,0) => (M ⟨0,hm⟩ ⟨0,hn⟩,⟨0,hm⟩,⟨0,hn⟩)
  | (0,l+1) =>
      have hl : (l+1) < n := by simp at h; rw [← h.2]; exact j.2
      if h1 : list_allZero (List.ofFn (M · ⟨l+1,hl⟩)) then findPivot_ij ⟨0,hm⟩ ⟨(l+2)%n,Nat.mod_lt (l+2) hn⟩
      else have h2 := nonzListHasNonz h1
        ((listFind (List.ofFn (M · ⟨l+1,hl⟩)) (fun x => x≠0) (by convert (nonzListHasNonz h1);simp)).1,⟨0,hm⟩,⟨l+1,hl⟩)
  | (k+1,0) =>
      have hk : (k+1) < m := by simp at h; rw [← h.1]; exact i.2
      if h1 : list_allZero (List.ofFn (M · ⟨0,hn⟩)) then findPivot_ij ⟨1%m,Nat.mod_lt 1 hm⟩ ⟨0,hn⟩
      else have h2 := nonzListHasNonz h1
        ((listFind (List.ofFn (M · ⟨0,hn⟩)) (fun x => x≠0) (by convert (nonzListHasNonz h1);simp)).1,⟨k+1,hk⟩,⟨0,hn⟩)
  | (k+1,l+1) =>
      have hl : (l+1) < n := by simp at h; rw [← h.2]; exact j.2
      have hk : (k+1) < m := by simp at h; rw [← h.1]; exact i.2
      if h1 : list_allZero (List.ofFn (M · ⟨l+1,hl⟩)) then findPivot_ij ⟨0,hm⟩ ⟨(l+2)%n,Nat.mod_lt (l+2) hn⟩
      else have h2 := nonzListHasNonz h1
        ((listFind (List.ofFn (M · ⟨l+1,hl⟩)) (fun x => x≠0) (by convert (nonzListHasNonz h1);simp)).1,⟨k+1,hk⟩,⟨l+1,hl⟩)
  termination_by (i.val, j.val) --Lexicographic order isn't working, have to show termination by another manner
  decreasing_by
  · simp_wf
    simp at h; rw [h.1]
    right
    -- apply Nat.sub_lt_sub_left j.2
    sorry
  · simp_wf
    left
    simp at h
    sorry
  · simp_wf
    simp at h; rw [h.1]
    left; linarith

#eval findPivot_ij !![1,2,3;4,5,6;7,8,9] (by linarith) (by linarith) 0 0

def pivotRowSwap : Matrix (Fin m) (Fin m) Rat :=
  if (findPivot M hm hn).1 = none then 1
  else eltRowSwap ⟨0,hm⟩ ((findPivot M hm hn).2).1

def pivotRowSwap_ij (i : Fin m) (j : Fin n) : Matrix (Fin m) (Fin m) Rat :=
  if (findPivot M hm hn).1 = none then 1
  else eltRowSwap ⟨0,hm⟩ ((findPivot M hm hn).2).1

#eval pivotRowSwap !![0,0,0;0,1,0;0,0,1] (by linarith) (by linarith)
#check Option.ne_none_iff_isSome

def pivotImprove : Matrix (Fin m) (Fin m) Rat :=
  if h : (findPivot M hm hn).1 = none then 1
  else eltScalarMul (1/(((findPivot M hm hn).1).get (Option.ne_none_iff_isSome.mp h))) ⟨0,hm⟩

#eval pivotImprove !![0,0,0;0,2,0;0,0,1] (by linarith) (by linarith)

def pivotColElimBelow : List (Matrix (Fin m) (Fin m) Rat) :=
  if (findPivot M hm hn).1 = none then [1]
  else List.ofFn fun i : Fin (m-1) => eltRowAdd ⟨i+1,Nat.add_lt_of_lt_sub i.2⟩ ⟨0,hm⟩ (- M ⟨i+1,Nat.add_lt_of_lt_sub i.2⟩ ((findPivot M hm hn).2).2)

#eval pivotColElimBelow !![1,0,0;0,1,0;0,0,1] (by linarith) (by linarith)
#eval pivotColElimBelow !![0,1,3;0,-1,6;0,2,9] (by linarith) (by linarith)

def exmat := !![4,-5,3,2;1,-1,-2,-6;4,-4,-14,(18:Rat)]
def piv := findPivot exmat (by linarith) (by linarith)
#eval piv
def e1 := pivotRowSwap exmat (by linarith) (by linarith)
#eval e1
def e2 := pivotImprove exmat (by linarith) (by linarith)
#eval e2
#eval e2 * e1 * exmat
def elist := pivotColElimBelow (e2 * e1 * exmat) (by linarith) (by linarith)
#eval elist
#eval (List.prod (elist.reverse++[e2,e1]))*exmat

#check Matrix.toBlock

def bot2x2 : Fin 2 → Fin 3
| 0 => 1
| 1 => 2


#eval !![1,2,3;4,5,6;7,8,9].submatrix bot2x2 bot2x2
