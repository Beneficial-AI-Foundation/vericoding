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
// Added a small lemma to unfold the definition of R for successive indices.
proof fn R_step(i: nat)
    ensures R(i + 1) == if R(i) > (i + 1) { R(i) - (i + 1) } else { R(i) + (i + 1) }
{
    // Unfold definition of R at index i+1
    assert(R(i + 1) ==
        if i + 1 == 0 {
            0nat
        } else if R((i + 1) - 1) > (i + 1) {
            R((i + 1) - 1) - (i + 1)
        } else {
            R((i + 1) - 1) + (i + 1)
        });
    // i+1 is never 0 (since i is nat), so simplify (i+1)-1 to i
    assert(i + 1 != 0);
    assert((i + 1) - 1 == i);
    assert(R(i + 1) == if R(i) > (i + 1) { R(i) - (i + 1) } else { R(i) + (i + 1) });
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut r: u64 = 0;
    let mut i: u64 = 0;
    while i < n
        invariant { i <= n && (r as nat) == R(i as nat) }
        decreases { (n as nat) - (i as nat) }
    {
        let k: u64 = i + 1;
        let old_r: u64 = r;
        if (old_r as nat) > (k as nat) {
            let res: u64 = old_r - k;
            proof {
                // From the loop invariant
                assert((old_r as nat) == R(i as nat));
                // The branch condition
                assert((old_r as nat) > (k as nat));
                // Unfold R at index k = i+1
                R_step(i as nat);
                assert(R(k as nat) ==
                    if R(i as nat) > (k as nat) {
                        R(i as nat) - (k as nat)
                    } else {
                        R(i as nat) + (k as nat)
                    });
                // Given R(i) > k, pick the subtraction case
                assert(R(i as nat) > (k as nat));
                assert(R(k as nat) == R(i as nat) - (k as nat));
                assert((res as nat) == (old_r as nat) - (k as nat));
                assert((res as nat) == R(k as nat));
            }
            r = res;
        } else {
            let res: u64 = old_r + k;
            proof {
                assert((old_r as nat) == R(i as nat));
                assert(!((old_r as nat) > (k as nat)));
                R_step(i as nat);
                assert(R(k as nat) ==
                    if R(i as nat) > (k as nat) {
                        R(i as nat) - (k as nat)
                    } else {
                        R(i as nat) + (k as nat)
                    });
                // Given not (R(i) > k), pick the addition case
                assert(!(R(i as nat) > (k as nat)));
                assert(R(k as nat) == R(i as nat) + (k as nat));
                assert((res as nat) == (old_r as nat) + (k as nat));
                assert((res as nat) == R(k as nat));
            }
            r = res;
        }
        i = k;
    }
    r
}
// </vc-code>

fn main() {}

}