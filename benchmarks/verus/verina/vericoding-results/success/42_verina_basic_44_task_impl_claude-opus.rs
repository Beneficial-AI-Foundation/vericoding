// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: i32) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed is_odd_exec to handle i32 modulo correctly */
fn is_odd_exec(n: i32) -> (result: bool)
    ensures result == is_odd(n)
{
    if n >= 0 {
        n % 2 == 1
    } else {
        n % 2 == -1
    }
}
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < a.len() && i % 2 == 1 ==> is_odd(a[i as int])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant to handle end-of-loop condition */
{
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i % 2 == 1 || i == a.len(),
            forall|j: int| 0 <= j < i && j % 2 == 1 ==> is_odd(a[j as int]),
        decreases if i < a.len() { a.len() - i } else { 0 }
    {
        if !is_odd_exec(a[i]) {
            return false;
        }
        if i + 2 < a.len() {
            i = i + 2;
        } else {
            i = a.len();
        }
    }
    true
}
// </vc-code>

}
fn main() {}