use builtin::*;
use builtin_macros::*;

verus! {

spec fn verifyNeg(a: Vec<int>, n: nat) -> nat
    requires n <= a.len()
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

// Helper lemma to relate verifyNeg with prefix counting
proof fn lemma_verify_neg_step(a: Vec<int>, n: nat)
    requires 0 < n <= a.len()
    ensures verifyNeg(a, n) == verifyNeg(a, n - 1) + (if a[n - 1] < 0 { 1 } else { 0 })
{
    // The proof follows directly from the definition of verifyNeg
}

fn CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    let mut cnt: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cnt == verifyNeg(a, i as nat),
    {
        proof {
            lemma_verify_neg_step(a, (i + 1) as nat);
        }
        
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