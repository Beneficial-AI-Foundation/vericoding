In this Kata you are a game developer and have programmed the #1 MMORPG(Massively Multiplayer Online Role Playing Game) worldwide!!! Many suggestions came across you to make the game better, one of which you are interested in and will start working on at once.

Players in the game have levels from 1 to 170, XP(short for experience) is required to increase the player's level and is obtained by doing all sorts of things in the game, a new player starts at level 1 with 0 XP. You want to add a feature that would enable the player to input a target level and the output would be how much XP the player must obtain in order for him/her to reach the target level...simple huh.

Create a function called ```xp_to_target_lvl``` that takes 2 arguments(```current_xp``` and ```target_lvl```, both as integer) and returns the remaining XP for the player to reach the ```target_lvl``` formatted as a rounded down integer.

Leveling up from level 1 to level 2 requires 314 XP, at first each level up requires 25% XP more than the previous level up, every 10 levels the percentage increase reduces by 1. See the examples for a better understanding.

Keep in mind that when players reach level 170 they stop leveling up but they continue gaining experience.

If one or both of the arguments are invalid(not given,  not in correct format, not in range...etc) return "Input is invalid.".

If the player has already reached the ```target_lvl``` return ```"You have already reached level target_lvl."```.

Examples:
```
xp_to_target_lvl(0,5) => XP from lvl1 to lvl2 = 314
                         XP from lvl2 to lvl3 = 314 + (314*0.25) = 392
                         XP from lvl3 to lvl4 = 392 + (392*0.25) = 490
                         XP from lvl4 to lvl5 = 490 + (490*0.25) = 612
                         XP from lvl1 to target_lvl = 314 + 392 + 490 + 612 = 1808
                         XP from current_xp to target_lvl = 1808 - 0 = 1808

xp_to_target_lvl(12345,17) => XP from lvl1 to lvl2 = 314                   
                               XP from lvl2 to lvl3 = 314 + (314*0.25) = 392
                               XP from lvl3 to lvl4 = 392 + (392*0.25) = 490
                               ...
                               XP from lvl9 to lvl10 = 1493 + (1493*0.25) = 1866 
                               XP from lvl10 to lvl11 = 1866 + (1866*0.24) = 2313 << percentage increase is 
                               ...                                                   reduced by 1 (25 - 1 = 24)
                               XP from lvl16 to lvl17 = 6779 + (6779*0.24) = 8405
                               XP from lvl1 to target_lvl = 314 + 392 + 490 + 612 + ... + 8405 = 41880
                               XP from current_xp to target_lvl = 41880 - 12345 = 29535

xp_to_target_lvl() => "Input is invalid."             }
xp_to_target_lvl(-31428.7,'47') => "Input is invalid." }> Invalid input
xp_to_target_lvl(83749,0) => "Input is invalid."   }

xp_to_target_lvl(2017,4) => "You have already reached level 4."
xp_to_target_lvl(0,1) => 'You have already reached level 1.'
```

Make sure you round down the XP required for each level up, rounding up will result in the output being slightly wrong.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded