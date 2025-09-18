// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed proof lemma and added complete specification for compute_element */
proof fn helper_lemma(x: Seq<i32>, i: int)
    requires
        0 <= i < x.len(),
    ensures
        -(x[i] + 1) == if x[i] == 0 { -1 } else if x[i] == -1 { 0 } else { -(x[i] + 1) },
{
}

spec fn compute_element(x: i32) -> i32 {
    -(x as int + 1) as i32
}

proof fn preserves_properties_lemma(x: i32)
    ensures
        compute_element(x) == -(x + 1),
        x == 0 ==> compute_element(x) == -1,
        x == -1 ==> compute_element(x) == 0,
        x != -1 ==> (x > 0 <==> compute_element(x) < 0),
{
}
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clause and refined loop invariant */
{
    let mut result = Vec::new();
    let n = x.len();
    let mut index: usize = 0;

    while index < n
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> result@[j] == compute_element(x@[j]),
            index <= n,
        decreases n - index,
    {
        proof { helper_lemma(x@, index as int); }
        result.push(compute_element(x[index]));
        index = index + 1;
    }

    result
}
// </vc-code>

}
fn main() {}