Bob has n heap(s) of gravel (initially there are exactly c piece(s) in each). He wants to do m operation(s) with that heaps, each maybe:

- adding pieces of gravel onto the heaps from u to v, exactly k pieces for each,
- or querying "how many pieces of gravel are there in the heap p now?".

-----Request-----
Help Bob do operations of the second type.

-----Input-----

- The first line contains the integers n,m,c, respectively.
- m following lines, each forms:

- S u v k to describe an operation of the first type.
- Q p to describe an operation of the second type.
(Each integer on a same line, or between the characters S, Q and the integers is separated by at least one space character)

-----Output-----
For each operation of the second type, output (on a single line) an integer answering to the respective query (follows the respective Input order).

-----Example-----Input:
7 5 0
Q 7
S 1 7 1
Q 3
S 1 3 1
Q 3
Output:
0
1
2

-----Limitations-----
- 0<n≤106
- 0<m≤250 000
- 0<u≤v≤n
- 0≤c,k≤109
- 0<p≤n

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded