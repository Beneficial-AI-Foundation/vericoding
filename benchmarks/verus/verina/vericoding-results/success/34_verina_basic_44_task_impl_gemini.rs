// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: i32) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed implementation to handle negative numbers using the remainder operator */
fn is_odd_exec(n: i32) -> (b: bool)
    ensures b == is_odd(n)
{
    n % 2 != 0
}
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < a.len() && i % 2 == 1 ==> is_odd(a[i as int])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes required, the logic is correct with the fixed helper */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i as int && j % 2 == 1 ==> is_odd(a[j as int]),
        decreases a.len() - i,
    {
        if i % 2 == 1 {
            if !is_odd_exec(a[i]) {
                return false;
            }
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}