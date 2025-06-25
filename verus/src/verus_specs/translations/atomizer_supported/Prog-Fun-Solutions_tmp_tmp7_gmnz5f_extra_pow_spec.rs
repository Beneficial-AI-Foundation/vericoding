// ATOM 
spec fn pow(a: int, e: nat) -> int {
    if e == 0 { 1 } else { a * pow(a, (e - 1) as nat) }
}

// SPEC 
pub fn Pow(a: nat, n: nat) -> (y: nat)
    ensures y == pow(a, n)
{
}