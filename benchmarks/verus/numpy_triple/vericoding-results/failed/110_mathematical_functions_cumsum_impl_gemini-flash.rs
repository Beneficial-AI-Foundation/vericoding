// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed, added comment to clarify */
// No helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
spec fn prefix_sum(a: Seq<i32>, i: int) -> int
    decreases i
{
    if i < 0 || i >= a.len() {
        0
    } else if i == 0 {
        a[0] as int
    } else {
        prefix_sum(a, i - 1) + (a[i] as int)
    }
}

fn numpy_cumsum(a: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        a.len() > 0 ==> result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] == result[i - 1] + a[i],
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == prefix_sum(a@, i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed mismatched types in invariant */
{
    let mut result: Vec<i32> = Vec::new();
    let mut sum: i32 = 0;
    let len = a.len();

    if len == 0 {
        return result;
    }

    result.push(a[0]);
    sum = a[0];

    let mut i: usize = 1;
    while i < len
        invariant
            0 < i,
            i <= len,
            result.len() == i,
            result@.len() == i as nat,
            sum as int == prefix_sum(a@, (i - 1) as int),
            forall|j: int| 0 <= j && j < i as int ==> result@.index(j) as int == prefix_sum(a@, j)
        decreases len - i
    {
        sum = sum + a[i];
        result.push(sum);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}