-- <vc-preamble>
def ValidProtocol (s : String) : Prop := s = "http" ∨ s = "ftp"

def IsValidDomainChar (c : Char) : Prop := c.isUpper ∨ c.isLower ∨ c.isDigit

def IsValidPathChar (c : Char) : Prop := c.isUpper ∨ c.isLower ∨ c.isDigit

def countChar (s : String) (c : Char) : Nat :=
  s.foldl (fun acc x => if x = c then acc + 1 else acc) 0

partial def containsSubstr (haystack needle : String) : Bool :=
  if needle.length = 0 then true
  else if haystack.length < needle.length then false
  else if haystack.take needle.length = needle then true
  else containsSubstr (haystack.drop 1) needle

partial def countSubstr (haystack needle : String) : Nat :=
  if needle.length = 0 then 0
  else if haystack.length < needle.length then 0
  else if haystack.take needle.length = needle
    then 1 + countSubstr (haystack.drop needle.length) needle
    else countSubstr (haystack.drop 1) needle
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_internet_address (s : String) : String := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem format_internet_address_starts_with_protocol (s : String) :
  (s.startsWith "http" ∨ s.startsWith "ftp") →
  (format_internet_address s).startsWith "http://" ∨
  (format_internet_address s).startsWith "ftp://" := 
sorry

theorem format_internet_address_preserves_protocol (s : String) :
  s.startsWith "http" → (format_internet_address s).startsWith "http://" := 
sorry

theorem format_internet_address_preserves_ftp (s : String) :
  s.startsWith "ftp" → (format_internet_address s).startsWith "ftp://" := 
sorry

theorem format_internet_address_contains_ru (s : String) :
  containsSubstr (format_internet_address s) ".ru" = true := 
sorry

theorem format_internet_address_single_ru (s : String) :
  countSubstr (format_internet_address s) ".ru" = 1 := 
sorry

theorem format_internet_address_path_slashes (s : String) :
  containsSubstr s "ru" = true →
  s.length > (s.length - (s.takeRight (s.length - 2)).length) + 2 →
  countChar (format_internet_address s) '/' = 3 :=
sorry
-- </vc-theorems>