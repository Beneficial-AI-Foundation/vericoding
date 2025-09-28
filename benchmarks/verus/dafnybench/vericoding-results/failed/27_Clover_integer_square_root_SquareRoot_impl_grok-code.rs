use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    let mut r_u64: u64 = 0;
    let mut r2_u64: u64 = 0;
    let n_u64 = n as u64;
    while r2_u64 <= n_u64 && r_u64 < 0x10000u64
        invariant
            (r_u64 as int) * (r_u64 as int) == (r2_u64 as int),
            r2_u64 <= n_u64,
            r_u64 < 0x10000u64,
        decreases 0x10000u64 - r_u64,
    {
        r_u64 += 1;
        r2_u64 += 2 * r_u64 - 1;
    }
    r_u64 = r_u64 - 1;
    let r = r_u64 as u32;
    proof! {
        if r_u64 == 0x10000u64 - 1 {
            assert(n_u64 as int >= (r_u64 as int) * (r_u64 as int));
            assert(n_u64 as int < (r_u64 as int + 1) * (r_u64 as int + 1));
        } else {
            assert(n_u64 as int < (r_u64 as int) * (r_u64 as int) || (r_u64 as int) >= 0x10000u64 as int);
        }
        let rr: u64 = r as u64;
        assert(rr as int * rr as int <= n_u64 as int);
        assert(n_u64 as int < (rr as int + 1) * (rr as int + 1));
    }
    r
}
// </vc-code>

fn main() {}

}