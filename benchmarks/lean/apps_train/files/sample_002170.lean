Haiku is a short form of Japanese poetry. A Haiku consists of three phrases with 5, 7 and 5 syllables, in this order.
Iroha is looking for X,Y,Z-Haiku (defined below) in integer sequences.
Consider all integer sequences of length N whose elements are between 1 and 10, inclusive. Out of those 10^N sequences, how many contain an X,Y,Z-Haiku?
Here, an integer sequence a_0, a_1, ..., a_{N-1} is said to contain an X,Y,Z-Haiku if and only if there exist four indices x, y, z, w (0 ≦ x < y < z < w ≦ N) such that all of the following are satisfied:
 - a_x + a_{x+1} + ... + a_{y-1} = X
 - a_y + a_{y+1} + ... + a_{z-1} = Y
 - a_z + a_{z+1} + ... + a_{w-1} = Z
Since the answer can be extremely large, print the number modulo 10^9+7.

-----Constraints-----
 - 3 ≦ N ≦ 40
 - 1 ≦ X ≦ 5
 - 1 ≦ Y ≦ 7
 - 1 ≦ Z ≦ 5

-----Input-----
The input is given from Standard Input in the following format:
N X Y Z

-----Output-----
Print the number of the sequences that contain an X,Y,Z-Haiku, modulo 10^9+7.

-----Sample Input-----
3 5 7 5

-----Sample Output-----
1

Here, the only sequence that contains a 5,7,5-Haiku is [5, 7, 5].

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded