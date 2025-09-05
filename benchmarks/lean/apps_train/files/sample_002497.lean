=====Problem Statement=====
There is an array of n integers. There are also 2 disjoint sets, A and B, each containing m integers. You like all the integers in set A and dislike all the integers in set B. Your initial happiness is 0. For each integer i in the array, if i ∈ A, you add 1 to your happiness. If i ∈ B, you add -1 to your happiness. Otherwise, your happiness does not change. Output your final happiness at the end.

Note: Since A and B are sets, they have no repeated elements. However, the array might contain duplicate elements.

=====Constraints=====
1≤n≤10^5
1≤m≤10^5
1≤Any integer in the input≤10^9

=====Input Format=====
The first line contains integers n and m separated by a space.
The second line contains n integers, the elements of the array.
The third and fourth lines contain m integers, A and B, respectively.

=====Output Format=====
Output a single integer, your total happiness.

def SetInt.contains (s : SetInt) (x : Int) : Bool :=
  match s with
  | mk list => list.contains x

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
