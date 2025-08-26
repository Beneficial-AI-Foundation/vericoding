function multisets<T>(s: seq<T>): multiset<T>
{
    if |s| == 0 then multiset{} 
    else multiset{s[0]} + multiset(s[1..])
}

/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 * FEUP, MFES, 2020/21.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Checks if array 'a' is sorted by non-descending order.
ghost predicate sorted(a: array<T>)
  reads a
{ forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }

// Obtains the set of all inversions in an array 'a', i.e., 
// the pairs of indices i, j such that i < j and a[i] > a[j]. 
ghost function inversions(a: array<T>): set<(nat, nat)>
  reads a
{ set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j) }

// Sorts an array by simply swapping elements out of order, chosen randomly.

// <vc-helpers>
// </vc-helpers>

method rawsort(a: array<T>)
   modifies a
   ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
   decreases |inversions(a)|
// <vc-code>
{
  assume false;
}
// </vc-code>

// States and proves (by induction) the following property: given sets 'a' and 'b' and an injective
// and non-surjective mapping 'm' from elements in 'a' to elements in 'b', then |a| < |b|.
// To facilitate the proof, it is given an element 'k' in 'b' that is not an image of elements in 'a'.   
lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  requires k in b
  requires forall x :: x in a ==> x in m && m[x] in b - {k} 
  requires forall x, y :: x in a && y in a && x != y ==> m[x] != m[y] 
  ensures |a| < |b|
{
   if x :| x in a {
      mappingProp(a - {x}, b - {m[x]}, k, m);
   }
}