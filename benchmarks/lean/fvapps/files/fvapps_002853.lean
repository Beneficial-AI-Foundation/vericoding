-- <vc-preamble>
def validUsers : List String := ["Timmy", "Alice", "Johny", "Roger", "Simon", "Admin"]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate (username password : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_username {username password : String}
  (h : username ∉ validUsers) :
  validate username password = "Wrong username or password!" :=
sorry

theorem injection_attempt {username password1 password2 : String}
  (h : username ∈ validUsers) :
  validate username (password1 ++ "||" ++ password2) = "Wrong username or password!" :=
sorry

theorem injection_attempt_slash {username password1 password2 : String}
  (h : username ∈ validUsers) :
  validate username (password1 ++ "//" ++ password2) = "Wrong username or password!" :=
sorry

theorem valid_login_timmy :
  validate "Timmy" "password" = "Successfully Logged in!" :=
sorry

theorem valid_login_alice :
  validate "Alice" "alice" = "Successfully Logged in!" :=
sorry

theorem valid_user_response {username password : String}
  (h : username ∈ validUsers) :
  validate username password = "Successfully Logged in!" ∨
  validate username password = "Wrong username or password!" :=
sorry
-- </vc-theorems>