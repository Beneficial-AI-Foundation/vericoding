function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// <vc-helpers>
/*
The original sum function in the preamble is duplicated in vc-helpers.
The preamble definition is recursive and computes sum(a[0]...a[i]).
The method cumsum's postcondition uses the preamble's sum function.
The sum function in vc-helpers is not needed.
Therefore, the function in vc-helpers can be removed.
*/
// </vc-helpers>

// <vc-spec>
method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    // when you change a  , that's not the same object than b . 
    //requires b.Length > 0 
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
// </vc-spec>
// <vc-code>
{
    var N := a.Length;
    if N > 0 {
        b[0] := a[0];
        var i := 1;
        while i < N
            invariant 1 <= i <= N
            invariant forall k | 0 <= k < i :: b[k] == sum(a, k)
        {
            b[i] := b[i-1] + a[i];
            i := i + 1;
        }
    }
}
// </vc-code>

