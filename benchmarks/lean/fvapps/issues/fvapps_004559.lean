-- <vc-preamble>
def CookieJar.is_open : CookieJar → Bool 
  | _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CookieJar.take (jar : CookieJar) : String :=
  sorry

structure SelfClosing (jar : CookieJar) where
  mk ::
-- </vc-definitions>

-- <vc-theorems>
theorem cookie_jar_initial_state (jar : CookieJar) : 
  jar.is_open = false := sorry 

theorem context_manager_always_closes (jar : CookieJar) (e : Exception) :
  ¬jar.is_open := sorry

theorem nested_context_managers (jar : CookieJar) 
  (ctx1 ctx2 : SelfClosing jar) :
  jar.is_open ∧
  (jar.is_open ∧ ¬jar.is_open) ∧
  ¬jar.is_open := sorry

theorem multiple_operations {α : Type} (ops : List α) (jar : CookieJar) 
  (h : ops.length > 0) :
  ∀ op ∈ ops,
    jar.take = "Cookie" ∧ 
    jar.is_open ∧
    ¬jar.is_open := sorry

theorem nested_depth (n : Nat) (jar : CookieJar) (h : n > 0 ∧ n ≤ 100) :
  jar.is_open ∧
  jar.take = "Cookie" ∧ 
  jar.is_open ∧
  ¬jar.is_open := sorry
-- </vc-theorems>