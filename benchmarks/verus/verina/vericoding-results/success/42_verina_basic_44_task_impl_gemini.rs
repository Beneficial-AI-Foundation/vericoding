// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: i32) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed is_odd_exec to correctly handle negative numbers */
fn is_odd_exec(n: i32) -> (b: bool)
    ensures
        b == is_odd(n),
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
    /* code modified by LLM (iteration 2): implemented loop to check all odd-indexed elements */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|j: int| 0 <= j < i && j % 2 == 1 ==> is_odd(a[j as int]),
        decreases
            a.len() - i,
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