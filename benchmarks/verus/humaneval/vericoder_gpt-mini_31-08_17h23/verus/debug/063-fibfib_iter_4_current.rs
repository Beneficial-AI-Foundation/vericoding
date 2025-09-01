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

fn fibfib_rec(n: nat) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> spec_fibfib(n) == ret.unwrap(),
    decreases n,
{
    if n == 0 {
        return Some(0);
    } else if n == 1 {
        return Some(0);
    } else if n == 2 {
        return Some(1);
    } else {
        let r1 = fibfib_rec((n - 1) as nat);
        let r2 = fibfib_rec((n - 2) as nat);
        let r3 = fibfib_rec((n - 3) as nat);

        if r1.is_none() || r2.is_none() || r3.is_none() {
            return None;
        }

        let v1: u128 = (r1.unwrap() as u128);
        let v2: u128 = (r2.unwrap() as u128);
        let v3: u128 = (r3.unwrap() as u128);

        let sum: u128 = v1 + v2 + v3;

        if sum > U32_MAX_U128 {
            return None;
        }

        let result_u32: u32 = (sum as u32);

        proof {
            // Use recursive ensures to relate runtime unwraps to spec values
            assert((r1.unwrap() as nat) == spec_fibfib((n - 1) as nat));
            assert((r2.unwrap() as nat) == spec_fibfib((n - 2) as nat));
            assert((r3.unwrap() as nat) == spec_fibfib((n - 3) as nat));

            // sum as nat equals sum of the spec values
            assert((sum as nat) == (r1.unwrap() as nat) + (r2.unwrap() as nat) + (r3.unwrap() as nat));
            // by definition of spec_fibfib for n >= 3
            assert(spec_fibfib(n) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
            assert((sum as nat) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
            assert((result_u32 as nat) == (sum as nat));
            assert((result_u32 as nat) == spec_fibfib(n));
        }

        return Some(result_u32);
    }
}
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
    let n: nat = x as nat;
    fibfib_rec(n)
}
// </vc-code>

fn main() {}
}