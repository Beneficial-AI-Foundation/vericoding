-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_codwars (url : String) : Bool := sorry

theorem valid_codwars_urls
  (protocol : String)
  (subdomains : List String)
  (path : String)
  (h1 : protocol = "http://" ∨ protocol = "https://" ∨ protocol = "")
  (h2 : ∀ s ∈ subdomains, s.data.all (λ c => 'a' ≤ c ∧ c ≤ 'z'))
  (h3 : subdomains.length ≤ 3)
  (h4 : path = "" ∨ (path.front = '/' ∧ path.data.all (λ c => ('a' ≤ c ∧ c ≤ 'z') ∨ 
                                                              ('0' ≤ c ∧ c ≤ '9') ∨
                                                              c = '/' ∨ c = '-' ∨ c = '_'))) :
  find_codwars (protocol ++ (String.intercalate "." subdomains) ++ 
                (if subdomains.length > 0 then "." else "") ++ 
                "codwars.com" ++ path) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_domains 
  (domain : String)
  (h1 : domain.length > 0)
  (h2 : domain.data.all (λ c => ('a' ≤ c ∧ c ≤ 'z') ∨ 
                                ('0' ≤ c ∧ c ≤ '9') ∨ 
                                c = '.' ∨ c = '-'))
  (h3 : ¬(∃ i, domain.take i ++ "codwars.com" ++ domain.drop (i + 11) = domain))
  (h4 : ∃ c ∈ domain.data, c = '.') :
  find_codwars domain = false := sorry

theorem case_sensitivity
  (text : String)
  (h1 : text.length > 0)
  (h2 : text.data.all (λ c => 'A' ≤ c ∧ c ≤ 'Z')) :
  find_codwars ("CODWARS.com/" ++ text) = false := sorry
-- </vc-theorems>