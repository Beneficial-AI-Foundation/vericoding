// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No logical change, helpers are sufficient for this implementation. */
spec fn around_one(val: i32) -> i32 { val }

proof fn lemma_around_one_monotonic(x: i32, y: i32)
    requires x <= y
    ensures around_one(x) <= around_one(y)
{}

proof fn lemma_around_one_properties(x: i32)
    ensures
        around_one(x) - 1 <= x && x <= around_one(x) + 1,
        x == 0 ==> around_one(x) == 0,
        x >= 0 ==> around_one(x) >= 0,
{}
// </vc-helpers>

// <vc-spec>
fn around(a: Vec<i32>, decimals: i32) -> (result: Vec<i32>)
    requires decimals == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> result[i] == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] <= a[j] ==> result[i] <= result[j],

        forall|i: int| 0 <= i < a.len() ==>
            result[i] - 1 <= a[i] && a[i] <= result[i] + 1,

        forall|i: int| 0 <= i < a.len() && a[i] >= 0 ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to prove loop termination. */
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> result@[k] == around_one(a@[k]),
        decreases a.len() - i
    {
        let val = a[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}