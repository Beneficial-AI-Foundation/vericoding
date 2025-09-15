// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed trigger attributes in invariants by moving them to the appropriate positions and using consistent indexing */
{
    let len = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall |j: int| #![trigger result[j]] (0 <= j < i && j != 4 && j != 7 ==> result[j] == a[j]),
            forall |j: int| #![trigger result[j]] (0 <= j < i && j == 4 ==> result[j] == a[j] + 3),
            forall |j: int| #![trigger result[j]] (0 <= j < i && j == 7 ==> result[j] == 516)
        decreases len - i
    {
        result.push(if i == 4 { a[i] + 3 } else if i == 7 { 516 } else { a[i] });
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}