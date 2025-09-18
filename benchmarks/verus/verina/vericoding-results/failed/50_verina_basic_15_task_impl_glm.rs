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
    /* code modified by LLM (iteration 2): fixed invariant syntax */
    let n = a.len();
    let mut i = 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant forall|j: int| { 0 <= j < i ==> a[j] + 1 != a[j+1] }
        decreases n - 1 - i
    {
        if a[i] + 1 == a[i+1] {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}