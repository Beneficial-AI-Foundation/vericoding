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
spec fn R_recursive_def(n: nat) -> nat
    decreases n // Added decreases clause
{
    if n == 0 {
        0nat
    } else {
        let prev_R = R_recursive_def((n - 1) as nat);
        if prev_R > n {
            (prev_R - n) as nat
        } else {
            (prev_R + n) as nat
        }
    }
}

proof fn lemma_R_is_R_recursive_def(n: nat)
    ensures R(n) == R_recursive_def(n)
    decreases n
{
    if n == 0 {
        assert(R(0) == 0);
        assert(R_recursive_def(0) == 0);
    } else {
        lemma_R_is_R_recursive_def((n - 1) as nat);
        assert(R((n - 1) as nat) == R_recursive_def((n - 1) as nat));
        if R((n - 1) as nat) > n {
            assert(R(n) == (R((n - 1) as nat) - n) as nat);
            assert(R_recursive_def(n) == (R_recursive_def((n - 1) as nat) - n) as nat);
        } else {
            assert(R(n) == (R((n - 1) as nat) + n) as nat);
            assert(R_recursive_def(n) == (R_recursive_def((n - 1) as nat) + n) as nat);
        }
    }
}

proof fn lemma_R_properties(prev_r: nat, i_val: nat)
    requires
        i_val > 0,
        prev_r == R_recursive_def((i_val - 1) as nat)
    ensures
        if prev_r > i_val {
            (prev_r - i_val) as nat == R_recursive_def(i_val)
        } else {
            (prev_r + i_val) as nat == R_recursive_def(i_val)
        }
{
    if prev_r > i_val {
        assert((prev_r - i_val) as nat == R_recursive_def(i_val)) by {
            lemma_R_is_R_recursive_def(i_val);
            // The following assertion is unnecessary as it's directly implied by the definition
            // assert(R_recursive_def(i_val) == (R_recursive_def((i_val - 1) as nat) - i_val) as nat);
        }
    } else {
        assert((prev_r + i_val) as nat == R_recursive_def(i_val)) by {
            lemma_R_is_R_recursive_def(i_val);
            // The following assertion is unnecessary as it's directly implied by the definition
            // assert(R_recursive_def(i_val) == (R_recursive_def((i_val - 1) as nat) + i_val) as nat);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    proof { lemma_R_is_R_recursive_def(n as nat); }

    let mut current_r: u64 = 0;
    let mut i: u64 = 0;

    while i < n
        invariant
            i <= n,
            current_r as nat == R_recursive_def(i as nat),
            i_as_nat_fits_u64: i == (i as nat) as u64, // Added to help with type conversions
            current_r_fits_u64: current_r == (current_r as nat) as u64 // Added to help with type conversions
    {
        i = i + 1;
        
        proof {
            // Need to assert that previous R_recursive_def used i-1 to match prev_r
            if i > 0 {
                assert (current_r as nat == R_recursive_def((i - 1) as nat));
            }
            lemma_R_properties(current_r as nat, i as nat);
        }

        if current_r > i {
            current_r = (current_r - i);
        } else {
            current_r = (current_r + i);
        }
        proof {
            // Intermediate assertion to help prove the final state of current_r
            if i > 0 && current_r as nat == R_recursive_def((i - 1) as nat) - i as nat {
                assert(R_recursive_def(i as nat) == (R_recursive_def((i - 1) as nat) - i as nat));
            }
            if i > 0 && current_r as nat == R_recursive_def((i - 1) as nat) + i as nat {
                assert(R_recursive_def(i as nat) == (R_recursive_def((i - 1) as nat) + i as nat));
            }
        }
        assert(current_r as nat == R_recursive_def(i as nat));
    }
    current_r
}
// </vc-code>

fn main() {}

}