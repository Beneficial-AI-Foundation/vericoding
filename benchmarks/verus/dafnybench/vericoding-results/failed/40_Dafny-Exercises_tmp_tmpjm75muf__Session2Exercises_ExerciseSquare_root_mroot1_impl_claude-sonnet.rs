use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_square_monotonic(a: u32, b: u32)
    requires a <= b
    ensures (a as int) * (a as int) <= (b as int) * (b as int)
{
}

fn lemma_square_bounds(r: u32, n: u32)
    requires r >= 1
    requires (r as int) * (r as int) > (n as int)
    ensures ((r - 1) as int) * ((r - 1) as int) <= (n as int)
{
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut r = 1u32;
    
    while (r as int) * (r as int) <= (n as int) && r < u32::MAX
        invariant 
            r >= 1,
            r <= n + 1,
            ((r - 1) as int) * ((r - 1) as int) <= (n as int),
        decreases (n as int) - (r as int) * (r as int)
    {
        let next_r = r + 1;
        if next_r == 0 || (next_r as int) * (next_r as int) > (n as int) {
            break;
        }
        r = next_r;
    }
    
    assert(r >= 1);
    assert(((r - 1) as int) * ((r - 1) as int) <= (n as int));
    
    if (r as int) * (r as int) <= (n as int) {
        assert(((r + 1) as int) * ((r + 1) as int) > (n as int));
        r
    } else {
        assert(r >= 1);
        assert(((r - 1) as int) * ((r - 1) as int) <= (n as int));
        assert((r as int) * (r as int) > (n as int));
        r - 1
    }
}
// </vc-code>

fn main() {}

}