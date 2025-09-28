// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error - removed invariant_except_break, simplified to standard while loop */
    let mut i: usize = 0;
    let mut result = true;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result == (forall|j: int| 0 <= j < i ==> n > a[j]),
        decreases a.len() - i,
    {
        if n <= a[i] {
            result = false;
            proof {
                assert(!result);
                assert(n <= a[i as int]);
                assert(0 <= i < a.len());
            }
        } else {
            proof {
                assert(n > a[i as int]);
            }
        }
        i = i + 1;
    }
    proof {
        if result {
            assert(i == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> n > a[j]);
        } else {
            assert(exists|j: int| 0 <= j < a.len() && n <= a[j]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}