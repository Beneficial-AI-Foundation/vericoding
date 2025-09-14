function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// <vc-helpers>
lemma sum_property(a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures sum(a, i) == a[i] + (if i == 0 then 0 else sum(a, i - 1))
{
    // This follows directly from the definition of sum
}

lemma sum_incremental(a: array<int>, i: int)
    requires 0 < i < a.Length
    ensures sum(a, i) == sum(a, i - 1) + a[i]
{
    // Follows from the recursive definition
}
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
    b[0] := a[0];
    var k := 1;
    while k < a.Length
        invariant 1 <= k <= a.Length
        invariant forall j | 0 <= j < k :: b[j] == sum(a, j)
    {
        b[k] := b[k-1] + a[k];
        sum_incremental(a, k);
        k := k + 1;
    }
}
// </vc-code>

