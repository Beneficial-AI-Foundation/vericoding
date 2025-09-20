-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidEmail (s : String) : Bool :=
  sorry

def numUniqueEmails (emails : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numUniqueEmails_bounds (emails : List String) :
  let result := numUniqueEmails emails
  0 ≤ result ∧ result ≤ emails.length :=
sorry

theorem numUniqueEmails_idempotent (emails : List String) :
  emails ≠ [] →
  numUniqueEmails (emails ++ emails) = numUniqueEmails emails :=
sorry

theorem numUniqueEmails_dot_invariant (email : String) (h : isValidEmail email) :
  let local_domain := email.splitOn "@"
  let dotted := String.join [local_domain.get! 0, "@", local_domain.get! 1]
  numUniqueEmails [email, dotted] = 1 :=
sorry

theorem numUniqueEmails_plus_invariant (email : String) (h : isValidEmail email) :
  let local_domain := email.splitOn "@"
  let plusAdded := String.join [local_domain.get! 0, "+anything@", local_domain.get! 1]
  numUniqueEmails [email, plusAdded] = 1 :=
sorry
-- </vc-theorems>