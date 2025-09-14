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
  var left := 0;
  var right := a.Length - 1;

  while left < right
    invariant 0 <= left <= right+1 <= a.Length
    invariant forall i :: 0 <= i < left ==> odd(a[i])
    invariant forall i :: right < i < a.Length ==> even(a[i])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    while left < right && odd(a[left])
      invariant left <= right
      invariant forall i :: 0 <= i < left ==> odd(a[i])
      invariant forall i :: right < i < a.Length ==> even(a[i])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      left := left + 1;
    }

    while left < right && even(a[right])
      invariant left <= right
      invariant forall i :: 0 <= i < left ==> odd(a[i])
      invariant forall i :: right < i < a.Length ==> even(a[i])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      right := right - 1;
    }

    if left < right {
      a[left], a[right] := a[right], a[left];
      left := left + 1;
      right := right - 1;
    }
  }
}
// </vc-code>

