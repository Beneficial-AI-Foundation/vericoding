// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

// <vc-helpers>
lemma MultisetPreservation(old_contents: seq<nat>, new_contents: seq<nat>, i: int, j: int)
  requires 0 <= i < |old_contents| && 0 <= j < |old_contents|
  requires |new_contents| == |old_contents|
  requires new_contents == old_contents[i := old_contents[j]][j := old_contents[i]]
  ensures multiset(new_contents) == multiset(old_contents)
{
  assert multiset(new_contents) == multiset(old_contents[i := old_contents[j]][j := old_contents[i]]);
}

lemma PartitionInvariant(a: array<nat>, left: int)
  requires 0 <= left <= a.Length
  requires forall k :: 0 <= k < left ==> odd(a[k])
  ensures forall k :: 0 <= k < left ==> odd(a[k])
{
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
  var right := a.Length;
  
  while left < right
    invariant 0 <= left <= right <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < left ==> odd(a[k])
    invariant forall k :: right <= k < a.Length ==> even(a[k])
    invariant ! exists i, j :: 0 <= i < left && right <= j < a.Length && even(a[i]) && odd(a[j])
  {
    if odd(a[left]) {
      left := left + 1;
    } else {
      right := right - 1;
      var temp := a[left];
      a[left] := a[right];
      a[right] := temp;
    }
  }
}
// </vc-code>

