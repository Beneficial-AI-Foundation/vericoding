// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause */
fn check_consecutive_at(a: &Vec<i32>, i: usize) -> (result: bool)
    requires 0 <= i < a.len() - 1
    ensures result <==> (a[i as int] + 1 == a[(i + 1) as int])
{
    a[i] + 1 == a[i + 1]
}
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
    /* code modified by LLM (iteration 5): fixed trigger by separating arithmetic from array access */
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] + 1 != #[trigger] a[j + 1]
        decreases a.len() - 1 - i
    {
        if check_consecutive_at(a, i) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}