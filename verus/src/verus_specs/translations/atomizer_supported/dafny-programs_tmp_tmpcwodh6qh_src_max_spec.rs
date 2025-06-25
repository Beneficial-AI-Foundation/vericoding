// SPEC 
pub fn Max(a: int, b: int) -> (c: int)
    ensures(a >= b ==> c == a)
    ensures(b >= a ==> c == b)
{
}

// SPEC 
pub fn MaxTest()
{
}

// ATOM 
pub fn max(a: int, b: int) -> int
{
    if a > b { a } else { b }
}

// SPEC 
pub fn maxTest()
{
}