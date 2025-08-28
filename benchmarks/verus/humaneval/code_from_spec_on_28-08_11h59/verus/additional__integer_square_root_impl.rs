use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn bounded_square(n: i32) -> int {
    if n <= 46340 { (n as int) * (n as int) } else { 2147483647 }
}

spec fn is_square_root(result: i32, n: i32) -> bool {
    result * result <= n && n < (result + 1) * (result + 1)
}

proof fn lemma_square_monotonic(a: i32, b: i32)
    requires 0 <= a <= b <= 46340,
    ensures (a as int) * (a as int) <= (b as int) * (b as int)
{
    if a == b {
        assert((a as int) * (a as int) == (b as int) * (b as int));
    } else {
        assert(a < b);
        assert((a as int) < (b as int));
        assert((a as int) * (a as int) <= (a as int) * (b as int));
        assert((a as int) * (b as int) <= (b as int) * (b as int));
    }
}

proof fn lemma_arithmetic_bounds(result: i32, n: i32)
    requires 
        result >= 1,
        result <= 46340,
        n >= 1,
        n <= 2147483647,
    ensures 
        result * result >= 0,
        (result + 1) * (result + 1) >= 0,
{
    assert(result >= 1);
    assert(result * result >= 1);
    assert(result + 1 >= 2);
    assert((result + 1) * (result + 1) >= 4);
}
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = 0;
    
    while result <= 46340 && (result as int) * (result as int) < n
        invariant
            result >= 0,
            result <= 46340 + 1,
            (result as int) * (result as int) <= n,
        decreases 46340 + 1 - result
    {
        if result < 46340 && (result + 1 < 46341) && ((result + 1) as int) * ((result + 1) as int) <= n {
            result = result + 1;
        } else {
            break;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}