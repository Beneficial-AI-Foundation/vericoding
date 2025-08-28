function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// <vc-helpers>
lemma sum_monotonic(a: array<int>, i: int, j: int)
    requires 0 <= i <= j < a.Length
    requires forall k | 0 <= k <= j :: a[k] >= 0
    ensures sum(a, i) <= sum(a, j)
{
    if i == j {
        // Base case: sum(a, i) == sum(a, j)
    } else {
        // Inductive case
        sum_monotonic(a, i, j - 1);
    }
}

lemma sum_property(a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures sum(a, i) == a[i] + (if i == 0 then 0 else sum(a, i - 1))
{
    // This follows directly from the definition of sum
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
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j | 0 <= j < i :: b[j] == sum(a, j)
        modifies b
    {
        b[i] := sum(a, i);
        i := i + 1;
    }
}
// </vc-code>
