// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
function AllOddIndicesAreOdd(a: array<int>): bool reads a {
  forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i])
}
// </vc-helpers>

// <vc-spec>
method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length && i % 2 == 1 ==> IsOdd(a[i]))
// </vc-spec>
// <vc-code>
{
  result := AllOddIndicesAreOdd(a);
}
// </vc-code>
