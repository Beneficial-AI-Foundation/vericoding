Indian National Olympiad in Informatics 2012
The Republic of Tutaria is celebrating its 37th year of independence. To mark the occasion, the nation is organising a contest where all its N citizens take part. The event has three tracks, a COBOL programming competition, pole vault, and a doughnut-eating competition. Each citizen takes part in these three tracks in the same order—a citizen starts with the programming competition, continues with the pole vault as soon as his or her COBOL masterpiece is ready, and then starts gorging on doughnuts as soon as the pole vault is done.
The Supreme Leader of Tutaria closely monitors all citizens and knows the exact amount of time each citizen will take in each of the three tracks. She wants to schedule the event so that it will finish as early as possible. However, the Republic of Tutaria has only one computer, and, as a result, only one person can participate in the COBOL programming event at a time. However, any number of people may simultaneously participate in the pole vault and doughnut-eating competitions.
The event works as follows. The Supreme Leader fixes the order in which contestants get access to the computer. At time 0, the first citizen in the list starts writing his or her COBOL program, while the remaining citizens wait for the computer to be free. As soon as the first citizen is done, he or she proceeds to the pole vault, and the second citizen gets the computer for the programming round. In general whenever the computer becomes free, the next citizen gets to use it. Whenever a citizen is done using the computer, he or she proceeds to the pole vault immediately, regardless of what the other citizens are doing. Similarly, whenever a citizen is done with the pole vault, he or she proceeds to the doughnut- eating track immediately, independently of the others. The event ends as soon as all the citizens have finished all the three tracks of the event.
For example, suppose N = 3, and the time they need for the three tracks are as follows:
Citizen id
COBOL
Pole vault
Doughnut-eating
1
18
7
6
2
23
10
27
3
20
9
14

If the citizens start at time 0 and proceed in the order 1,2,3, then citizen 1 will finish at time 18+7+6 = 31, citizen 2 will finish at time 18+23+10+27 = 78, and citizen 3 will finishattime18+23+20+9+14=84. Theeventendsattimemax(31,78,84)=84.
On the other hand, if the citizens proceed in the order 2,3,1, you can check that the event ends at max(60, 66, 74) = 74. The Supreme Leader of Tutaria wants to fix the order in which the citizens proceed so that the event ends as early as possible. You can check that in this case 74 is the earliest time at which the event can end.

-----Input format-----
The first line of input has a single integer, N, the number of citizens of the Republic of Tutaria. The next N lines contain 3 space-separated integers each: line i gives the time taken by the citizen i for COBOL programming, pole vault, and doughnut-eating respectively.

-----Output format-----
The output should have a single line with a single integer, the earliest time at which the event can end.

-----Test Data-----
The testdata is grouped into two subtasks with the following constraints on the inputs.
• Subtask 1 [30 points] : 1 ≤ N ≤ 3000.
• Subtask 2 [70 points] : 1 ≤ N ≤ 200000.
In both the subtasks, all the numbers in the input (except possibly N) are in the range 1 to 10000, inclusive.

-----Example-----
Here is the sample input and output corresponding to the example above.

-----Sample input-----
3
18 7 6 
23 10 27
20 9 14

-----Sample output-----
74

-----Note:----- Your program should not print anything other than what is specified in the output format. Please remove all diagnostic print statements before making your final submission. A program with extraneous output will be treated as incorrect!

def sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
