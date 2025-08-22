
// ATOM 

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}


// SPEC 

method minMethod(a: int, b: int) returns (c: int)
    ensures c <= a && c <= b
    ensures c == a || c == b
    // Ou encore:
    ensures c == min(a, b)
{
}


// ATOM 

ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}



// Return a minimum of a.
// SPEC 


// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;

    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
{
}


// SPEC 

method Main(){
}




