// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

// <vc-helpers>
lemma lemma_even_odd_partition (a: array<nat>, k: int)
  requires 0 <= k <= a.Length
  requires forall l :: 0 <= l < k ==> odd(a[l])
  requires forall l :: k <= l < a.Length ==> even(a[l])
  ensures ! exists x, y :: 0 <= x < y < a.Length && even(a[x]) && odd(a[y])
{
  // This lemma directly proves the postcondition for a given range [i, j]
  // if the elements within this range are already partitioned.
  // No explicit proof steps are needed here for Dafny for this simple property;
  // Dafny's SMT solver can usually deduce this from the universal quantifiers.
}
// </vc-helpers>

// <vc-spec>
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
// </vc-spec>
// <vc-code>
{
  var left := 0;
  var right := a.Length - 1;

  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant left >= right || left <= right + 1 // Added an invariant to handle the case where left_new could be greater than right_new as loop terminates when left > right
    invariant forall k :: 0 <= k < left ==> odd(a[k])
    invariant forall k :: right < k < a.Length ==> even(a[k])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    while left <= right && odd(a[left])
      invariant 0 <= left <= a.Length
      invariant -1 <= right < a.Length
      invariant forall k :: 0 <= k < left ==> odd(a[k])
      invariant forall k :: right < k < a.Length ==> even(a[k])
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant left <= right + 1 // Added to reflect the relationship between left and right as left can exceed right by 1
    {
      left := left + 1;
    }

    while left <= right && even(a[right])
      invariant 0 <= left <= a.Length
      invariant -1 <= right < a.Length
      invariant forall k :: 0 <= k < left ==> odd(a[k])
      invariant forall k :: right < k < a.Length ==> even(a[k])
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant left <= right + 1 // Added to reflect the relationship between left and right
    {
      right := right - 1;
    }

    if left < right
    {
      // a[left] must be even because the first inner loop stopped.
      // a[right] must be odd because the second inner loop stopped.
      // Thus, swap them.
      var temp := a[left];
      a[left] := a[right];
      a[right] := temp;
      
      left := left + 1;
      right := right - 1;
    }
  }

  lemma_even_odd_partition(a, left);
}
// </vc-code>

