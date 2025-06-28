use builtin::*;
use builtin_macros::*;

verus! {

spec fn verifyNeg(a: Vec<int>, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if a[n - 1] < 0 {
        1 + verifyNeg(a, n - 1)
    } else {
        verifyNeg(a, n - 1)
    }
}

fn CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    let mut cnt: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            cnt == verifyNeg(a, i),
    {
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    
    cnt
}

fn main() {
}

}