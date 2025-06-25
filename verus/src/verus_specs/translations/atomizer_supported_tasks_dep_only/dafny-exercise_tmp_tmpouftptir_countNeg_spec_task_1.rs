// ATOM 
spec fn verifyNeg(a: &[i32], idx: usize) -> nat
    requires 0 <= idx <= a.len()
    decreases idx
{
    if idx == 0 { 0 }
    else { verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 { 1 } else { 0 }) }
}

// SPEC 
pub fn CountNeg(a: &[i32]) -> (cnt: nat)
    ensures cnt == verifyNeg(a, a.len())
{
}