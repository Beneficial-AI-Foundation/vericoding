// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
