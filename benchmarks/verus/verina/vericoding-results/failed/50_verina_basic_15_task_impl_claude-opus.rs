// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting - use i32 directly instead of casting to int */
    if a.len() <= 1 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> a[j] + 1 != a[(j + 1) as int],
        decreases a.len() - 1 - i,
    {
        if a[i] + 1 == a[i + 1] {
            assert(0 <= i < a.len() - 1);
            assert(a[i] + 1 == a[(i + 1) as int]);
            return true;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() - 1 ==> a[j] + 1 != a[(j + 1) as int]);
    false
}
// </vc-code>

}
fn main() {}