// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { (n % 2) + popcount(n / 2) }
}
// </vc-preamble>

// <vc-helpers>
proof fn popcount_bound(n: nat, bits: nat)
    requires n < pow2(bits)
    ensures popcount(n) <= bits
    decreases bits
{
    if bits == 0 {
        assert(n == 0);
    } else {
        assert(bits >= 1);
        let bits_minus_1 = (bits - 1) as nat;
        assert(n / 2 < pow2(bits_minus_1));
        popcount_bound(n / 2, bits_minus_1);
        assert(popcount(n) == (n % 2) + popcount(n / 2));
        assert(n % 2 <= 1);
        assert(popcount(n / 2) <= bits_minus_1);
    }
}

/* helper modified by LLM (iteration 5): Added pow2_8 lemma to prove pow2(8) == 256 */
proof fn pow2_8()
    ensures pow2(8) == 256
{
    assert(pow2(8) == 2 * pow2(7));
    assert(pow2(7) == 2 * pow2(6));
    assert(pow2(6) == 2 * pow2(5));
    assert(pow2(5) == 2 * pow2(4));
    assert(pow2(4) == 2 * pow2(3));
    assert(pow2(3) == 2 * pow2(2));
    assert(pow2(2) == 2 * pow2(1));
    assert(pow2(1) == 2 * pow2(0));
    assert(pow2(0) == 1);
}

/* helper modified by LLM (iteration 5): Call pow2_8 lemma before assertion */
proof fn popcount_u8_bound(n: u8)
    ensures popcount(n as nat) <= 8
{
    assert((n as nat) < 256);
    pow2_8();
    assert(256 == pow2(8));
    popcount_bound(n as nat, 8);
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8) -> (r: u8)
    ensures r as nat == popcount(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed */
    let mut count: u8 = 0;
    let mut m = n;
    
    proof {
        popcount_u8_bound(n);
    }
    
    while m != 0
        invariant
            count as nat + popcount(m as nat) == popcount(n as nat),
            count as nat <= popcount(n as nat),
            popcount(n as nat) <= 8
        decreases m
    {
        if m % 2 == 1 {
            count = count + 1;
        }
        m = m / 2;
    }
    
    count
}
// </vc-code>


}

fn main() {}