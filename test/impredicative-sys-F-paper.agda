
{-
-------------------------------------------------------------------------------
  "PAPER" PROOF:

  By induction on types T, and for all (e : T)
  I will define
  (app e e₁ e₂ ... eₙ) for well typed args, as well as
  e'[x ↦ e] for any well typed e'.

  The latter is easy, as it only depends on the former.

  For the former, cases on T:
  -- T = A ⇒ B.
    then e = λ x . e'
    e₁ : A. Recurse with (e₁ : A) to get e'[x ↦ e₁] : B.
    Next, recurse with (e'[x ↦ e₁] : B) to apply rest of args.
  -- T = ∀ X . A.
    then e = Λ X . e'
    recurse on (e : T)
    then at the end, sub in X.

    THIS DOESNT WORK, BECAUSE THE REMAINING ARGUMENTS MAY NOT TYPE WITHOUT SUBBING IN X.
  -- T = X.  So sub(X) = X
    the can't be any well typed args. Keep in mind that X is at level n,
    and so sub(X) = X.
  -- T = cumu A. So, sub(cumu A) = cumu (sub(A))
    then e = cumu e'. Simply recurse with [n-1, sub(A), idSub, e']
    so need idSub(sub(A)) = sub(A)
-------------------------------------------------------------------------------

-}
