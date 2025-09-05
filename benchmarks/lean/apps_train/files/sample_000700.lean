-----Problem-----

Suppose there is a circle. There are N Juice shops on that circle. Juice shops are numbered 0 to N-1 (both inclusive). You have two pieces of information corresponding to each of the juice shop:
(1) the amount of Juice that a particular Juice shop can provide and 
(2) the distance from that juice shop to the next juice shop.

Initially, there is a man with a bottle of infinite capacity carrying no juice. He can start the tour at any of the juice shops. Calculate the first point from where the man will be able to complete the circle. Consider that the man will stop at every Juice Shop. The man will move one kilometer for each litre of the juice.

-----Input-----
- 
The first line will contain the value of N.

- 
The next N lines will contain a pair of integers each, i.e. the amount of juice that a juice shop can provide(in litres) and the distance between that juice shop and the next juice shop.

-----Output-----

An integer which will be the smallest index of the juice shop from which he can start the tour.

-----Constraints-----
- 
					1 ≤ N ≤ 105
- 
					1 ≤ amt of juice, distance  ≤ 109

-----Sample Input-----
3

1 5

10 3

3 4

-----Sample Output-----
1

-----Explanation-----

			He can start the tour from the SECOND Juice shop.
		 p { text-align:justify }

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
