//ATOM_PLACEHOLDER_min

//ATOM_PLACEHOLDER_minMethod

//ATOM_PLACEHOLDER_minFunction

//IMPL Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
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

//ATOM_PLACEHOLDER_Main