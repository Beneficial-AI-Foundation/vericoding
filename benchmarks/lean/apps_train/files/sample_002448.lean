=====Function Descriptions=====
If we want to add a single element to an existing set, we can use the .add() operation.
It adds the element to the set and returns 'None'.

=====Example=====
>>> s = set('HackerRank')
>>> s.add('H')
>>> print s
set(['a', 'c', 'e', 'H', 'k', 'n', 'r', 'R'])
>>> print s.add('HackerRank')
None
>>> print s
set(['a', 'c', 'e', 'HackerRank', 'H', 'k', 'n', 'r', 'R'])

=====Problem Statement=====
Apply your knowledge of the .add() operation to help your friend Rupal.
Rupal has a huge collection of country stamps. She decided to count the total number of distinct country stamps in her collection. She asked for your help. You pick the stamps one by one from a stack of N country stamps.
Find the total number of distinct country stamps.

=====Input Format=====
The fist line contains an integer N, the total number of country stamps.
The next N lines contains the name of the country where the stamp is from.

=====Constraints=====
0<N<1000

=====Output Format=====
Output the total number of distinct country stamps on a single line.

def count_distinct_stamps (stamps : List String) : Nat := sorry

theorem count_distinct_stamps_bounded (stamps : List String) : 
  count_distinct_stamps stamps ≤ stamps.length := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
