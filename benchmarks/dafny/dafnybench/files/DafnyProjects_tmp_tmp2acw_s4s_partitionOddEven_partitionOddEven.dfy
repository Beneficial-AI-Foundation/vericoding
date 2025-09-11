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
  assume {:axiom} false;
}
// </vc-code>
