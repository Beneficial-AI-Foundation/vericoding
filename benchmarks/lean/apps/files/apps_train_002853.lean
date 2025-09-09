def validate (username password : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def validUsers : List String := ["Timmy", "Alice", "Johny", "Roger", "Simon", "Admin"]

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

/-
info: 'Successfully Logged in!'
-/
-- #guard_msgs in
-- #eval validate "Timmy" "password"

/-
info: 'Wrong username or password!'
-/
-- #guard_msgs in
-- #eval validate "Timmy" "h4x0r"

/-
info: 'Successfully Logged in!'
-/
-- #guard_msgs in
-- #eval validate "Alice" "alice"

/-
info: 'Wrong username or password!'
-/
-- #guard_msgs in
-- #eval validate "Timmy" "password"||""==""

/-
info: 'Wrong username or password!'
-/
-- #guard_msgs in
-- #eval validate "Admin" "gs5bw"||1==1//"

-- Apps difficulty: introductory
-- Assurance level: unguarded