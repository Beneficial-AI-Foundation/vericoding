use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mul_strict_increasing(x: int, y: int)
    requires 0 <= y && y < x,
    ensures x * x > y
{
    // From y < x and y >= 0 we get x > 0, and since x is an integer, x >= 1, so x - 1 >= 0.
    assert(x > 0);
    assert(x - 1 >= 0);
    // x*(x-1) >= 0
    assert(x * (x - 1) >= 0);
    // x*x = x + x*(x-1) >= x > y, so x*x > y
    assert(x * x == x + x * (x - 1));
    assert(x > y);
    assert(x * x > y);
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut rr: u32 = 0u32;
    while ({
        let next = (rr as u64) + 1u64;
        next * next <= (n as u64)
    }) {
        invariant ((rr as u64) * (rr as u64) <= (n as u64));
        invariant rr <= n;
        decreases (n - rr);
        {
            rr = rr + 1;
        }
    }

    proof {
        assert(((rr as u64) * (rr as u64)) <= (n as u64));
        assert(!({
            let next = (rr as u64) + 1u64;
            next * next <= (n as u64)
        }));

        let r_int: int = rr as int;
        let n_i: int = n as int;

        // From the u64 inequality we can conclude the corresponding int inequality
        assert(r_int * r_int <= n_i);
        assert(n_i < (r_int + 1) * (r_int + 1));
    }

    rr
}
// </vc-code>

fn main() {}

}