function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// <vc-helpers>
lemma SumLemma(a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures sum(a, i) == if i == 0 then a[0] else a[i] + sum(a, i - 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    // when you change a  , that's not the same object than b . 
    //requires b.Length > 0 
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
// </vc-spec>
// </vc-spec>

// <vc-code>
method CumSum(a: array<int>, b: array<int>)
    requires a.Length == b.Length && a.Length > 0 && a != b
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{
    b[0] := a[0];
    var k := 1;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall i | 0 <= i < k :: b[i] == sum(a, i)
    {
        b[k] := a[k] + b[k-1];
        k := k + 1;
    }
}
// </vc-code>
