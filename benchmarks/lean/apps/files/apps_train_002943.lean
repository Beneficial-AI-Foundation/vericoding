/-
Comprised of a team of five incredibly brilliant women, "The ladies of ENIAC" were the first “computors” working at the University of Pennsylvania’s Moore School of Engineering (1945). Through their contributions, we gained the first software application and the first programming classes! The ladies of ENIAC were inducted into the WITI Hall of Fame in 1997!

Write a function which reveals "The ladies of ENIAC" names, so that you too can add them to your own hall of tech fame!

To keep: only alpha characters, space characters and exclamation marks.  
To remove: numbers and these characters: ```%$&/£?@```

Result should be all in uppercase.
-/

-- <vc-helpers>
-- </vc-helpers>

def rad_ladies (s : String) : String := sorry

theorem rad_ladies_name_preserved {s : String} (h : s ≠ "") :
  let result := rad_ladies (s ++ "!")
  (result.startsWith s) ∧ (result.endsWith "!") := sorry

theorem rad_ladies_idempotent (s : String) :
  rad_ladies (rad_ladies s) = rad_ladies s := sorry

/-
info: 'KAY MCNULTY!'
-/
-- #guard_msgs in
-- #eval rad_ladies "k?%35a&&/y@@@5599 m93753&$$$c$n///79u??@@%l?975$t?%5y%&$3$1!"

/-
info: 'MARLYN WESCOFF!'
-/
-- #guard_msgs in
-- #eval rad_ladies "9?9?9?m335%$@a791%&$r$$$l@53$&y&n%$5@ $5577w&7e931%s$c$o%%%f351f??%!%%"

/-
info: 'FRAN BILAS!'
-/
-- #guard_msgs in
-- #eval rad_ladies "%&$557f953//1/$@%r%935$$a@3111$@???%n???5 $%157b%///$i%55&31@l?%&$$a%@$s5757!$$%%%%53"

-- Apps difficulty: introductory
-- Assurance level: unguarded