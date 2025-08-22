
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

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}
Function


// Return a minimum of a.
// ATOM 

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}
Array

//ATOM_PLACEHOLDER_Main



