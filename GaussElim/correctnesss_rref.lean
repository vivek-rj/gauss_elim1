import GaussElim.ge_test2vec

/-
Preliminary lemmas
1.
2. when a matrix is multiplied by the list of elementary matrices outputted by
  the rref function, it gives the same result as the 2nd output of the rref function (How?)
3. each element of the list is an elementary matrix
4.
-/

/-
Proving that a matrix that goes through the row-reduced echelon form algorithm is in its
row-reduced echelon form

1. Show that the result is row-reduced
  a. each row is either all 0 or has its first nonzero entry as 1
    aa. The nonzero entry corresponding to the first nonzero column is the first nonzero
      entry of the corresponding row
    ab. multiplication of M with findpivot_ij i j makes it so that the (i,j)th entry is
      either 0 or 1
    ac. the (i,j)th step of rowEchelonStep does not change the rows and columns before i
      and j
    ad. the (i,j)th step of rowEchelonStep makes the (i,j)th entry as 0 or 1 and every
      entry below it 0


2. Show that the zero rows are last

3. Show that the columns corresponding to the nonzero rows are in increasing order

-/


namespace ElemOp

#check if_neg
#check dite_eq_left_iff
#check dite

example (p : Prop) [Decidable p] (b : ¬p → α) (h : (dite p (fun _ => a) b) = a) : p := by
  contrapose h
  simp
  use h
  -- rw [ite_eq_left_iff] at h
  -- contrapose h
  -- push_neg
  -- exact ⟨h,h0⟩

def f := fun x => cond (x==0) 3 4
example (x : Nat) (h : f x = 3) : x=0 := by
  unfold f at h
  rw?

theorem rowEchelonStep_reduceRow (i : Fin m) (j : Fin n) :
  (rowEchelonStep M i j) i j = 0 ∨ (rowEchelonStep M i j) i j = 1 := by
  cases h : findPivot_ij M i j
  · unfold rowEchelonStep
    simp [h]
    let M' := botRightij M i j
    have h1 : findNonzCol M' = (colVecofMat M').length := by
      -- contrapose h
      -- unfold findPivot_ij
      -- unfold_let at h ⊢
      -- simp only [dite_eq_left_iff]
      unfold findPivot_ij at h
      unfold_let at h
      rw [dite_eq_left_iff] at h
      contrapose h
      push_neg
      use h
      simp
