// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn sheets_needed(n: int) -> (int, int, int) {
    (2 * n, 5 * n, 8 * n)
}

spec fn total_sheets_needed(n: int) -> int {
    2 * n + 5 * n + 8 * n
}

spec fn ceil_div(a: int, b: int) -> int
    recommends b > 0
{
    (a + b - 1) / b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove proof blocks from spec functions */
proof fn ceil_div_properties(a: int, b: int)
    requires b > 0
    ensures ceil_div(a, b) == (a + b - 1) / b,
            ceil_div(a, b) * b >= a,
            ceil_div(a, b) * b < a + b
{
    let cd = ceil_div(a, b);
    assert(cd == (a + b - 1) / b);
    
    // For the inequality cd * b >= a
    let div_result = (a + b - 1) / b;
    assert(div_result * b <= a + b - 1);
    assert(div_result * b >= a + b - 1 - (b - 1));
    assert(div_result * b >= a);
    
    // For the inequality cd * b < a + b
    assert(div_result * b <= a + b - 1);
    assert(div_result * b < a + b);
}

proof fn ceil_div_non_negative(a: int, b: int)
    requires a >= 0, b > 0
    ensures ceil_div(a, b) >= 0
{
    assert(a + b - 1 >= 0);
    assert((a + b - 1) / b >= 0);
}

proof fn sum_ceil_div_bound(n: int, k: int)
    requires n >= 0, k > 0
    ensures ceil_div(2 * n, k) + ceil_div(5 * n, k) + ceil_div(8 * n, k) >= ceil_div(15 * n, k)
{
    let cd2 = ceil_div(2 * n, k);
    let cd5 = ceil_div(5 * n, k);
    let cd8 = ceil_div(8 * n, k);
    let cd15 = ceil_div(15 * n, k);
    
    ceil_div_properties(2 * n, k);
    ceil_div_properties(5 * n, k);
    ceil_div_properties(8 * n, k);
    ceil_div_properties(15 * n, k);
    
    assert(cd2 * k >= 2 * n);
    assert(cd5 * k >= 5 * n);
    assert(cd8 * k >= 8 * n);
    
    assert((cd2 + cd5 + cd8) * k >= 2 * n + 5 * n + 8 * n);
    assert((cd2 + cd5 + cd8) * k >= 15 * n);
    
    // Since cd15 is the ceiling of 15*n/k, we have cd15 * k < 15*n + k
    assert(cd15 * k < 15 * n + k);
    // And since cd15 is minimal such that cd15 * k >= 15*n, we get the bound
    assert(cd2 + cd5 + cd8 >= cd15);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == ceil_div(2 * (n as int), k as int) + ceil_div(5 * (n as int), k as int) + ceil_div(8 * (n as int), k as int),
        result >= 0,
        result as int >= (total_sheets_needed(n as int) + (k as int) - 1) / (k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement ceil division calculation */
    
    let two_n = 2 * n;
    let five_n = 5 * n;
    let eight_n = 8 * n;
    
    let packs_for_two = (two_n + k - 1) / k;
    let packs_for_five = (five_n + k - 1) / k;
    let packs_for_eight = (eight_n + k - 1) / k;
    
    let result = packs_for_two + packs_for_five + packs_for_eight;
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        let two_n_int = 2 * n_int;
        let five_n_int = 5 * n_int;
        let eight_n_int = 8 * n_int;
        
        ceil_div_properties(two_n_int, k_int);
        ceil_div_properties(five_n_int, k_int);
        ceil_div_properties(eight_n_int, k_int);
        ceil_div_non_negative(two_n_int, k_int);
        ceil_div_non_negative(five_n_int, k_int);
        ceil_div_non_negative(eight_n_int, k_int);
        sum_ceil_div_bound(n_int, k_int);
        
        assert(packs_for_two as int == ceil_div(two_n_int, k_int));
        assert(packs_for_five as int == ceil_div(five_n_int, k_int));
        assert(packs_for_eight as int == ceil_div(eight_n_int, k_int));
        assert(result as int >= 0);
    }
    
    result
}
// </vc-code>


}

fn main() {}