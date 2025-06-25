// Ghost
// ATOM 

// Ghost
pub open spec fn Double(val: int) -> int {
    2 * val
}

// SPEC 

pub fn TestDouble(val: int) -> (val2: int)
    ensures val2 == Double(val)
{
}