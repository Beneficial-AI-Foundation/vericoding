// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed loop variable to usize and added necessary casts for spec context. */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> (is_odd(j) ==> is_odd(a@[j])),
        decreases (a.len() - i) as int
    {
        if is_odd(i as int) {
            if !is_odd(a[i]) {
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