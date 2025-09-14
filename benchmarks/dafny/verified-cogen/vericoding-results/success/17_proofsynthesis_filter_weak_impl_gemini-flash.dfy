// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Myfun4(x: array<int>, y: array<int>) returns ()
    requires y.Length == 0
    ensures forall k :: 0 <= k < y.Length ==> y[k] % 3 == 0 && y[k] in x[..]
// </vc-spec>
// <vc-code>
{
    // Since y.Length == 0, the postcondition `forall k :: 0 <= k < y.Length ==> ...`
    // is vacuously true, as there are no k such that 0 <= k < y.Length.
    // Therefore, no operations on `y` or `x` are needed to satisfy the postcondition.
}
// </vc-code>
