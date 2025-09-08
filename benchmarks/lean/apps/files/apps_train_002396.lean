/-
Every email consists of a local name and a domain name, separated by the @ sign.
For example, in alice@leetcode.com, alice is the local name, and leetcode.com is the domain name.
Besides lowercase letters, these emails may contain '.'s or '+'s.
If you add periods ('.') between some characters in the local name part of an email address, mail sent there will be forwarded to the same address without dots in the local name.  For example, "alice.z@leetcode.com" and "alicez@leetcode.com" forward to the same email address.  (Note that this rule does not apply for domain names.)
If you add a plus ('+') in the local name, everything after the first plus sign will be ignored. This allows certain emails to be filtered, for example m.y+name@email.com will be forwarded to my@email.com.  (Again, this rule does not apply for domain names.)
It is possible to use both of these rules at the same time.
Given a list of emails, we send one email to each address in the list.  How many different addresses actually receive mails? 

Example 1:
Input: ["test.email+alex@leetcode.com","test.e.mail+bob.cathy@leetcode.com","testemail+david@lee.tcode.com"]
Output: 2
Explanation: "testemail@leetcode.com" and "testemail@lee.tcode.com" actually receive mails

Note:

1 <= emails[i].length <= 100
1 <= emails.length <= 100
Each emails[i] contains exactly one '@' character.
All local and domain names are non-empty.
Local names do not start with a '+' character.
-/

def isValidEmail (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def numUniqueEmails (emails : List String) : Nat :=
  sorry

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

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_unique_emails ["test.email+alex@leetcode.com", "test.e.mail+bob.cathy@leetcode.com", "testemail+david@lee.tcode.com"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_unique_emails ["a@leetcode.com", "b@leetcode.com", "c@leetcode.com"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_unique_emails ["test.email+alex@leetcode.com", "test.email@leetcode.com"]

-- Apps difficulty: introductory
-- Assurance level: guarded