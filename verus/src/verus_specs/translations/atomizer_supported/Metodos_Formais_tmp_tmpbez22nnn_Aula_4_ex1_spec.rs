// ATOM 
pub open spec fn Par(n: int) -> bool
{
    n % 2 == 0
}

// SPEC 
pub fn FazAlgo(a: int, b: int) -> (x: int, y: int)
    requires a >= b && Par(a - b)
{
}