// ATOM 
pub open spec fn max(x: nat, y: nat) -> nat
{
    if x < y { y } else { x }
}

// SPEC 

pub fn slow_max(a: nat, b: nat) -> (z: nat)
    ensures z == max(a, b)
{
}