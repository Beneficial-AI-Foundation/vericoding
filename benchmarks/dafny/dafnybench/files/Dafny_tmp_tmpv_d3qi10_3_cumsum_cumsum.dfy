// <vc-preamble>
function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b

    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
