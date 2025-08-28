use vstd::prelude::*;

verus! {

spec fn R(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        0nat 
    } else if R((n-1) as nat) > n { 
        (R((n-1) as nat) - n) as nat
    } else { 
        (R((n-1) as nat) + n) as nat
    }
}

// <vc-helpers>
spec fn R_fits_u64(n: nat) -> bool {
    R(n) <= 0xFFFFFFFFFFFFFFFF
}

proof fn lemma_R_bounded(n: nat)
    requires n <= 0xFFFFFFFFFFFFFFFF
    ensures R_fits_u64(n)
    decreases n
{
    if n == 0 {
        assert(R(0) == 0);
    } else {
        lemma_R_bounded((n-1) as nat);
        let prev = R((n-1) as nat);
        if prev > n {
            assert(R(n) == (prev - n) as nat);
            assert(R(n) < prev);
        } else {
            assert(R(n) == (prev + n) as nat);
            assert(R(n) <= prev + n);
            assert(n <= 0xFFFFFFFFFFFFFFFF);
            assert(prev <= 0xFFFFFFFFFFFFFFFF);
        }
    }
}

proof fn lemma_R_invariant_helper(i: nat, curr: nat)
    requires i >= 1
    requires curr == R((i-1) as nat)
    requires R_fits_u64(i)
    ensures if curr > i { R(i) == curr - i } else { R(i) == curr + i }
{
    let prev = R((i-1) as nat);
    assert(curr == prev);
    if prev > i {
        assert(R(i) == (prev - i) as nat);
        assert(R(i) == curr - i);
    } else {
        assert(R(i) == (prev + i) as nat);
        assert(R(i) == curr + i);
    }
}

proof fn lemma_R_bounded_for_all_up_to(n: nat)
    requires n <= 0xFFFFFFFFFFFFFFFF
    ensures forall |k: nat| k <= n ==> R_fits_u64(k)
    decreases n
{
    if n == 0 {
        lemma_R_bounded(0);
    } else {
        lemma_R_bounded_for_all_up_to(n - 1);
        lemma_R_bounded(n);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut i: u64 = 1;
    let mut curr: u64 = 0;
    
    proof {
        lemma_R_bounded_for_all_up_to(n as nat);
    }
    
    while i <= n
        invariant 
            1 <= i <= n + 1,
            curr == R((i-1) as nat),
            forall |k: nat| k <= n ==> R_fits_u64(k)
        decreases n - i
    {
        proof {
            lemma_R_invariant_helper(i as nat, curr as nat);
            assert(R_fits_u64(i as nat));
            assert(R(i as nat) <= 0xFFFFFFFFFFFFFFFF);
        }
        
        if curr > i {
            curr = curr - i;
        } else {
            curr = curr + i;
        }
        
        proof {
            assert(R(i as nat) == curr);
        }
        
        i = i + 1;
    }
    
    curr
}
// </vc-code>

fn main() {}

}