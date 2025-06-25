use vstd::prelude::*;

spec fn verifyNeg(a: &[int], idx: int) -> nat
    recommends 0 <= idx <= a.len()
{
    if idx == 0 { 0 }
    else { verifyNeg(a, idx - 1) + if a[idx as usize - 1] < 0 { 1 } else { 0 } }
}

pub fn CountNeg(a: &[int]) -> (cnt: usize)
    ensures cnt == verifyNeg(a, a.len() as int)
{
    unimplemented!()
}

pub fn Main()
{
}