
//ATOM_PLACEHOLDER_min

//ATOM_PLACEHOLDER_minMethod

//ATOM_PLACEHOLDER_minFunction


// Return a minimum of a.
// SPEC 


// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;

    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
{
}


//ATOM_PLACEHOLDER_Main



