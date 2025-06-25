// SPEC 
pub fn Abs(x: int) -> (y: int)
    requires()
    ensures(|y: int| y >= 0)
    ensures(|y: int| x >= 0 ==> x == y)
    ensures(|y: int| x < 0 ==> -x == y)
    ensures(|y: int| y == abs(x))
{
}

// ATOM 
spec fn abs(x: int) -> int {
    if x > 0 { x } else { -x }
}

// SPEC 
pub fn Testing()
    requires()
    ensures()
{
}

//ATOM_PLACEHOLDER_MultiReturn

//ATOM_PLACEHOLDER_Max