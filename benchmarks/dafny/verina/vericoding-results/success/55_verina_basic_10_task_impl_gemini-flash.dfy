// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate is_greater_than_all(n: int, a: array<int>) 
    reads a
    requires a.Length > 0
{
    forall i :: 0 <= i < a.Length ==> n > a[i]
}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
    result := is_greater_than_all(n, a);
}
// </vc-code>
