use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sqr_mono(x: int, y: int)
    requires
        x >= 0,
        y >= 0,
    ensures
        x <= y <==> x * x <= y * y,
{
    if x <= y {
        assert(x * x <= y * y);
    } else {
        assert(y < x);
        assert(y * y < x * x);
    }
}

proof fn lemma_sqr_diff(x: int)
    requires
        x >= 0,
    ensures
        (x + 1) * (x + 1) == x * x + 2 * x + 1,
{
}

spec fn sqrt_bound(n: int) -> int
    recommends n >= 0
{
    (n as nat).sqrt() as int
}

proof fn sqrt_bound_properties(n: int)
    requires n >= 0,
    ensures
        let r = sqrt_bound(n);
        r >= 0 && r * r <= n < (r + 1) * (r + 1),
{
    let r = sqrt_bound(n);
    assert(r >= 0) by {
        assert(n as nat >= 0nat);
    }
    assert(r * r <= n);
    assert(n < (r + 1) * (r + 1));
}
// </vc-helpers>

// <vc-spec>
fn mroot1(n: u32) -> (r: u32) //Cost O(root n)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut r: u32 = 0;
    let mut k: u32 = 0;
    
    #[verifier::spec] let n_int = n as int;
    
    while k <= n
        invariant
            r >= 0,
            k == r * r,
            (r as int) * (r as int) <= n_int,
    {
        if k + 2 * r + 1 <= n {
            proof {
                lemma_sqr_diff(r as int);
            }
            r = r + 1;
            k = k + 2 * r - 1;
        } else {
            break;
        }
    }
    
    proof {
        sqrt_bound_properties(n_int);
        assert(n_int < ((r + 1) as int) * ((r + 1) as int));
    }
    
    r
}
// </vc-code>

fn main() {}

}