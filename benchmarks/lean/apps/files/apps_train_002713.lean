/-
Oh no! Ghosts have reportedly swarmed the city. It's your job to get rid of them and save the day!

In this kata, strings represent buildings while whitespaces within those strings represent ghosts.

So what are you waiting for? Return the building(string) without any ghosts(whitespaces)!

Example:

Should return:

If the building contains no ghosts, return the string:
-/

-- <vc-helpers>
-- </vc-helpers>

def ghostbusters (s : String) : String := sorry

theorem ghostbusters_with_spaces (s : String) (h : String.contains s ' ') :
  ghostbusters s = s.replace " " "" := sorry

theorem ghostbusters_without_spaces (s : String) (h : ¬String.contains s ' ') :
  ghostbusters s = "You just wanted my autograph didn't you?" := sorry

/-
info: 'Factory'
-/
-- #guard_msgs in
-- #eval ghostbusters "Factor y"

/-
info: 'Office'
-/
-- #guard_msgs in
-- #eval ghostbusters "O  f fi ce"

/-
info: "You just wanted my autograph didn't you?"
-/
-- #guard_msgs in
-- #eval ghostbusters "BusStation"

-- Apps difficulty: introductory
-- Assurance level: unguarded