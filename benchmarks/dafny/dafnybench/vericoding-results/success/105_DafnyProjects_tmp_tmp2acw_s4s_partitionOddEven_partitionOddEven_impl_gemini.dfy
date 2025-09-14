// <vc-preamble>
predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }
// </vc-preamble>

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
  var i: nat := 0;
  var j: nat := a.Length;
  while i < j
    invariant 0 <= i <= j <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < i ==> odd(a[k])
    invariant forall k :: j <= k < a.Length ==> even(a[k])
    decreases j - i
  {
    if odd(a[i]) {
      i := i + 1;
    } else { // a[i] is even
      j := j - 1;
      a[i], a[j] := a[j], a[i];
    }
  }
}
// </vc-code>
