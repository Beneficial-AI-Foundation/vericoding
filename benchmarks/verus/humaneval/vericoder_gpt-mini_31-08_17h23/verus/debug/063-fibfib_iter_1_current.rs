use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
const U32_MAX_U128: u128 = (core::u32::MAX) as u128;
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: nat = x as nat;
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(0);
    }
    if n == 2 {
        return Some(1);
    }

    // runtime values (u128 to avoid u32 overflow during computation)
    let mut a_r: u128 = 0; // v_{i-3}
    let mut b_r: u128 = 0; // v_{i-2}
    let mut c_r: u128 = 1; // v_{i-1}

    // ghost/spec values mirroring runtime values
    let mut a_g: nat = 0;
    let mut b_g: nat = 0;
    let mut c_g: nat = 1;

    let mut i: nat = 3;

    while i <= n
        invariant 3 <= i && i <= n + 1
        invariant a_g == spec_fibfib((i - 3) as nat)
        invariant b_g == spec_fibfib((i - 2) as nat)
        invariant c_g == spec_fibfib((i - 1) as nat)
        invariant (a_r as nat) == a_g
        invariant (b_r as nat) == b_g
        invariant (c_r as nat) == c_g
        decreases (n - i)
    {
        // compute next
        let d_r: u128 = a_r + b_r + c_r;
        let d_g: nat = a_g + b_g + c_g;

        // relate runtime sum to ghost sum
        proof {
            // casting sum of u128s to nat equals sum of casts
            assert((a_r + b_r + c_r) as nat == (a_r as nat) + (b_r as nat) + (c_r as nat));
            assert(d_r as nat == d_g);
            // by definition of spec_fibfib for indices >= 3
            assert(d_g == spec_fibfib(i as nat));
        }

        // if value exceeds u32 max, return None
        if d_r > U32_MAX_U128 {
            return None;
        }

        // shift for next iteration: now index increases by 1
        a_r = b_r;
        b_r = c_r;
        c_r = d_r;

        a_g = b_g;
        b_g = c_g;
        c_g = d_g;

        i = i + 1;
    }

    // after loop, i == n + 1, so c_g == spec_fibfib(n)
    proof {
        assert(i == n + 1);
        assert(c_g == spec_fibfib(n));
        assert((c_r as nat) == c_g);
    }

    // c_r holds the value for n and has been checked to be <= U32_MAX_U128 in the loop if it would exceed
    if c_r <= U32_MAX_U128 {
        let result_u32: u32 = (c_r as u32);
        // final proof that runtime result equals spec
        proof {
            assert((result_u32 as nat) == (c_r as nat));
            assert((c_r as nat) == c_g);
            assert(c_g == spec_fibfib(n));
        }
        return Some(result_u32);
    } else {
        return None;
    }
    // impl-end
}
// </vc-code>

fn main() {}
}