// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length - 1;
  while i <= j
    invariant 0 <= i <= j+1 <= a.Length
    invariant forall k :: 0 <= k < i ==> odd(a[k])
    invariant forall k :: j+1 <= k < a.Length ==> even(a[k])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if odd(a[i]) {
      i := i + 1;
    } else if even(a[j]) {
      j := j - 1;
    } else {
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>

