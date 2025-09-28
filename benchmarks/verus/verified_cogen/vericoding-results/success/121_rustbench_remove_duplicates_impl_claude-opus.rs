// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to both loops */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| #![auto] 0 <= k < result.len() ==> in_array(a@, result[k]),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases a.len() - i,
    {
        let current = a[i];
        let mut found = false;
        let mut j = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found <==> exists|k: int| 0 <= k < j && result[k] == current,
            decreases result.len() - j,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j = j + 1;
        }
        if !found {
            result.push(current);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}