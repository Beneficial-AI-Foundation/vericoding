use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut r = 0;
    while r < 65535
        invariant r as int * r as int <= n as int
        decreases 65535 - r
    {
        let next = r + 1;
        let next_sq = (next as u64) * (next as u64);
        if next_sq <= n as u64 {
            r = next;
        } else {
            break;
        }
    }
    r
}
// </vc-code>

fn main() {}

}