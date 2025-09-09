-- <vc-helpers>
-- </vc-helpers>

def mask_pii (s : String) : String := sorry 

theorem phone_masking_10_digits
  (phone : String)
  (h : phone.length = 10)
  (h₁ : ∀ c ∈ phone.data, c.isDigit) :
  let last4 := phone.drop (phone.length - 4)
  mask_pii phone = s!"***-***-{last4}" := sorry

theorem phone_masking_longer
  (phone : String) 
  (h : phone.length > 10)
  (h₁ : ∀ c ∈ phone.data, c.isDigit) :
  let masked := mask_pii phone
  let last4 := phone.drop (phone.length - 4)
  -- masked starts with +
  (masked.front = '+') ∧ 
  -- ends with last 4 digits
  (masked.takeRight 4 = last4) ∧
  -- contains - and *
  (∃ c ∈ masked.data, c = '-') ∧
  (∃ c ∈ masked.data, c = '*') := sorry

theorem email_masking
  (email : String)
  (h : email = "LeetCode@LeetCode.com") :
  mask_pii email = "l*****e@leetcode.com" := sorry

/-
info: 'l*****e@leetcode.com'
-/
-- #guard_msgs in
-- #eval mask_pii "LeetCode@LeetCode.com"

/-
info: '***-***-7890'
-/
-- #guard_msgs in
-- #eval mask_pii "1(234)567-890"

/-
info: '+**-***-***-5678'
-/
-- #guard_msgs in
-- #eval mask_pii "86-(10)12345678"

-- Apps difficulty: interview
-- Assurance level: unguarded