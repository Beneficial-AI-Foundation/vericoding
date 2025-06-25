// ATOM 

spec fn min(a: int, b: int) -> int
    ensures |result: int| result <= a && result <= b
    ensures |result: int| result == a || result == b
{
    if a < b { a } else { b }
}


// SPEC 

pub fn minMethod(a: int, b: int) -> (c: int)
    ensures c <= a && c <= b,
    ensures c == a || c == b,
    // Ou encore:
    ensures c == min(a, b),
{
}


// ATOM 

spec fn min(a: int, b: int) -> int
    ensures |result: int| result <= a && result <= b
    ensures |result: int| result == a || result == b
{
    if a < b { a } else { b }
}


// Return a minimum of a.
// ATOM 

spec fn min(a: int, b: int) -> int
    ensures |result: int| result <= a && result <= b
    ensures |result: int| result == a || result == b
{
    if a < b { a } else { b }
}

//ATOM_PLACEHOLDER_Main