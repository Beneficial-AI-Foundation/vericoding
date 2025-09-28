// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn in_range(i: int, len: int) -> bool { 
    0 <= i < len
}

proof fn vec_index_valid<T>(v: &Vec<T>, i: int) -> bool 
    requires v@.len() >= 0
    ensures result == (0 <= i < v@.len())
{
    0 <= i < v@.len()
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
    /* code modified by LLM (iteration 5): Fixed syntax error in spec and simplified implementation */
    let mut result = a.clone();
    
    proof {
        assert(vec_index_valid(a, 4));
        assert(vec_index_valid(a, 7));
    }
    
    result.set(4, a[4] + 3);
    result.set(7, 516);
    result
}
// </vc-code>

}
fn main() {}