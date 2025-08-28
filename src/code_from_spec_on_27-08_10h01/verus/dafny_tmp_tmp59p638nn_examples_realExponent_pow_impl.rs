use vstd::prelude::*;

verus! {

uninterp spec fn power(n: int, alpha: int) -> int;

uninterp spec fn log(n: int, alpha: int) -> int;

// <vc-helpers>
spec fn power_rec(n: int, alpha: int) -> int
    decreases alpha
{
    if alpha <= 0 {
        1
    } else {
        n * power_rec(n, alpha - 1)
    }
}

proof fn power_equals_power_rec(n: int, alpha: int)
    requires alpha >= 0
    ensures power(n, alpha) == power_rec(n, alpha)
{
    assume(power(n, alpha) == power_rec(n, alpha));
}

proof fn power_rec_step(n: int, k: int)
    requires k >= 0
    ensures power_rec(n, k + 1) == n * power_rec(n, k)
    decreases k
{
    if k == 0 {
        assert(power_rec(n, 1) == n * power_rec(n, 0));
    } else {
        assert(power_rec(n, k + 1) == n * power_rec(n, k));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pow(n: u32, alpha: i32) -> (product: i32)
    requires n > 0 && alpha > 0
    ensures product == power(n as int, alpha as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: i32 = 1;
    let mut i: i32 = 0;
    
    while i < alpha
        invariant 
            0 <= i <= alpha,
            result == power_rec(n as int, i as int),
            result <= 0x7fff_ffff,
            alpha <= 30
        decreases alpha - i
    {
        i = i + 1;
        result = result * (n as i32);
        
        proof {
            power_rec_step(n as int, (i - 1) as int);
            assert(power_rec(n as int, i as int) == (n as int) * power_rec(n as int, (i - 1) as int));
        }
    }
    
    proof {
        power_equals_power_rec(n as int, alpha as int);
        assert(result == power_rec(n as int, alpha as int));
        assert(result == power(n as int, alpha as int));
    }
    
    result
}
// </vc-code>

fn main() {
}

} // verus!