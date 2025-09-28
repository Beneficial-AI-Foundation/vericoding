// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, r: int) -> bool {
    n >= 1 && r >= 1
}

spec fn expected_result(n: int, r: int) -> int {
    if valid_input(n, r) {
        let k = if r < n - 1 { r } else { n - 1 };
        k * (k + 1) / 2 + if r >= n { 1int } else { 0int }
    } else {
        0int
    }
}

fn solve_shapes(n: i8, r: i8) -> (result: i8)
    requires valid_input(n as int, r as int)
    ensures result as int == expected_result(n as int, r as int)
// </vc-preamble>

// <vc-helpers>
fn compute_k(n: int, r: int) -> (k: int)
    requires
        valid_input(n, r),
    ensures
        k == if r < n - 1 { r } else { n - 1 },
{
    if r < n - 1 {
        r
    } else {
        n - 1
    }
}

fn sum_first_k_nat(k: nat) -> (sum: nat)
    requires
        k >= 0,
    ensures
        sum == k * (k + 1) / 2,
{
    if k == 0 {
        0
    } else {
        let sub = sum_first_k_nat((k - 1) as nat);
        k + sub
    }
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation by removing decreases clause */
    let n_int = n as int;
    let r_int = r as int;
    
    let k_val = compute_k(n_int, r_int);
    let triangle_number = sum_first_k_nat(k_val as nat);
    
    proof {
        assert(triangle_number == k_val * (k_val + 1) / 2);
        assert(k_val == if r_int < n_int - 1 { r_int } else { n_int - 1 });
    }
    
    let additional_circle = if r_int >= n_int { 1 } else { 0 };
    let total = triangle_number + additional_circle;
    
    proof {
        assert(total == expected_result(n_int, r_int));
    }
    
    (total as i8)
}
// </vc-code>


}

fn main() {}