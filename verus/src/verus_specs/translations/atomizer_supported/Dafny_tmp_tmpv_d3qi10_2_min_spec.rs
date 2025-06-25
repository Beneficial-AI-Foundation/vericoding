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

spec fn minFunction(a: int, b: int) -> int
    ensures |result: int| result <= a && result <= b
    ensures |result: int| result == a || result == b
{
    if a < b { a } else { b }
}



// Return a minimum of a.
// SPEC 


// Return a minimum of a.
pub fn minArray(a: &[int]) -> (m: int)
    requires a.len() > 0,
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k as usize],
    ensures exists|k: int| 0 <= k < a.len() && m == a[k as usize],
{
}


// SPEC 

pub fn Main()
{
}