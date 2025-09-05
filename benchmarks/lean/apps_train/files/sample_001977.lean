In the official contest this problem has a different statement, for which jury's solution was working incorrectly, and for this reason it was excluded from the contest. This mistake have been fixed and the current given problem statement and model solution corresponds to what jury wanted it to be during the contest.

Vova and Lesha are friends. They often meet at Vova's place and compete against each other in a computer game named The Ancient Papyri: Swordsink. Vova always chooses a warrior as his fighter and Leshac chooses an archer. After that they should choose initial positions for their characters and start the fight. A warrior is good at melee combat, so Vova will try to make the distance between fighters as small as possible. An archer prefers to keep the enemy at a distance, so Lesha will try to make the initial distance as large as possible.

There are n (n is always even) possible starting positions for characters marked along the Ox axis. The positions are given by their distinct coordinates x_1, x_2, ..., x_{n}, two characters cannot end up at the same position.

Vova and Lesha take turns banning available positions, Vova moves first. During each turn one of the guys bans exactly one of the remaining positions. Banned positions cannot be used by both Vova and Lesha. They continue to make moves until there are only two possible positions remaining (thus, the total number of moves will be n - 2). After that Vova's character takes the position with the lesser coordinate and Lesha's character takes the position with the bigger coordinate and the guys start fighting.

Vova and Lesha are already tired by the game of choosing positions, as they need to play it before every fight, so they asked you (the developer of the The Ancient Papyri: Swordsink) to write a module that would automatically determine the distance at which the warrior and the archer will start fighting if both Vova and Lesha play optimally.

-----Input-----

The first line on the input contains a single integer n (2 ≤ n ≤ 200 000, n is even) — the number of positions available initially. The second line contains n distinct integers x_1, x_2, ..., x_{n} (0 ≤ x_{i} ≤ 10^9), giving the coordinates of the corresponding positions.

-----Output-----

Print the distance between the warrior and the archer at the beginning of the fight, provided that both Vova and Lesha play optimally.

-----Examples-----
Input
6
0 1 3 7 15 31

Output
7

Input
2
73 37

Output
36

-----Note-----

In the first sample one of the optimum behavior of the players looks like that:  Vova bans the position at coordinate 15;  Lesha bans the position at coordinate 3;  Vova bans the position at coordinate 31;  Lesha bans the position at coordinate 1. 

After these actions only positions 0 and 7 will remain, and the distance between them is equal to 7.

In the second sample there are only two possible positions, so there will be no bans.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
