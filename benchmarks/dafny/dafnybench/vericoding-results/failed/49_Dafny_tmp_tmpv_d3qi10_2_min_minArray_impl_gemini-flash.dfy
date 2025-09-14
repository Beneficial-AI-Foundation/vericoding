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
function minVal(a: int, b: int): int
    ensures minVal(a, b) <= a && minVal(a, b) <= b
    ensures minVal(a, b) == a || minVal(a, b) == b
{
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
// </vc-spec>
// <vc-code>
{
    var minimum := a[0];
    var i := 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k | 0 <= k < i :: minimum <= a[k]
        invariant (exists k_val | 0 <= k_val < i :: minimum == a[k_val]) || i == 1
    {
        if a[i] < minimum {
            minimum := a[i];
        }
        i := i + 1;
    }
    return minimum;
}
// </vc-code>

