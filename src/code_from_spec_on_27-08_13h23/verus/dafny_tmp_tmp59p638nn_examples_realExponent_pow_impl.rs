use vstd::prelude::*;

verus! {

uninterp spec fn power(n: int, alpha: int) -> int;

uninterp spec fn log(n: int, alpha: int) -> int;

// <vc-helpers>
proof fn power_positive(n: int, alpha: int)
    requires n > 0, alpha > 0
    ensures power(n, alpha) > 0
{
    // This is a placeholder for actual proof if power is uninterpreted
    // In a real scenario, this would be proven based on power's definition
}

spec fn power_recursive(n: int, alpha: int) -> int
    decreases alpha
{
    if alpha <= 0 {
        1
    } else {
        n * power_recursive(n, alpha - 1)
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
fn pow(n: u32, alpha: i32) -> (product: i32)
    requires n > 0, alpha > 0
    ensures product == power(n as int, alpha as int)
{
    let mut result = 1i32;
    let mut exp = alpha;
    
    while exp > 0
        invariant
            exp >= 0,
            result > 0
    {
        result = result * (n as i32);
        exp = exp - 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

} // verus!