// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add precondition helper for overflow checking */
spec fn can_add_safely(x: i32, y: i32) -> bool {
    x <= i32::MAX - y && x >= i32::MIN - y
}

proof fn prove_safe_addition(x: i32, y: i32)
    requires y == 3,
    ensures can_add_safely(x, y),
{
    assert(i32::MIN <= -2147483645);
    assert(i32::MAX >= 2147483644);
    assert(x >= i32::MIN >= -2147483648);
    assert(x <= i32::MAX <= 2147483647);
    assert(x <= i32::MAX - 3);
    assert(x >= i32::MIN - 3);
}
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use proof helper to establish overflow safety */
    let mut result = a.clone();
    let old_value_4 = result[4];
    
    proof {
        prove_safe_addition(old_value_4, 3);
        assert(can_add_safely(old_value_4, 3));
        assert(old_value_4 + 3 <= i32::MAX);
        assert(old_value_4 + 3 >= i32::MIN);
    }
    
    result.set(4, old_value_4 + 3);
    result.set(7, 516);
    
    proof {
        assert(result[4] == a[4] + 3);
        assert(result[7] == 516);
        assert(result.len() == a.len());
    }
    
    result
}
// </vc-code>

}
fn main() {}