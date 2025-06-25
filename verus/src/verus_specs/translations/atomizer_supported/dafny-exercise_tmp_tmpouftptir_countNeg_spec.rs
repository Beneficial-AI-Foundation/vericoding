use vstd::prelude::*;

verus! {

spec fn verifyNeg(a: &[int], idx: int) -> nat
    recommends 0 <= idx <= a.len()
{
    if idx == 0 { 0 }
    else { verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 { 1 } else { 0 }) }
}

pub fn CountNeg(a: &[int]) -> (cnt: nat)
    ensures cnt == verifyNeg(a, a.len() as int)
{
}

pub fn Main()
{
}

}