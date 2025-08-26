method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var oddEnd := 0;
  var current := 0;
  
  while current < a.Length
    invariant 0 <= oddEnd <= current <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < oddEnd ==> odd(a[k])
    invariant forall k :: oddEnd <= k < current ==> even(a[k])
    invariant ! exists i, j :: 0 <= i < j < current && even(a[i]) && odd(a[j])
  {
    if odd(a[current]) {
      if oddEnd != current {
        a[oddEnd], a[current] := a[current], a[oddEnd];
      }
      oddEnd := oddEnd + 1;
    }
    current := current + 1;
  }
}
// </vc-code>

predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }