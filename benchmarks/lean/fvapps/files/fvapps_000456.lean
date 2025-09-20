-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mask_pii (s : String) : String := sorry 

theorem phone_masking_10_digits
  (phone : String)
  (h : phone.length = 10)
  (h₁ : ∀ c ∈ phone.data, c.isDigit) :
  let last4 := phone.drop (phone.length - 4)
  mask_pii phone = s!"***-***-{last4}" := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>