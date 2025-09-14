function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}


ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}


// Return a minimum of a.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
// </vc-spec>
// <vc-code>
{
    m := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k | 0 <= k < i :: m <= a[k]
        invariant exists k | 0 <= k < i :: m == a[k]
    {
        if a[i] < m {
            m := a[i];
        }
        i := i + 1;
    }
}
// </vc-code>

