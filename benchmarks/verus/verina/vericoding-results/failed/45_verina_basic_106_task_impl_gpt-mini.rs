// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma for int indexing */
fn vec_index_trivial(v: &Vec<i32>, i: int)
    requires
        0 <= i,
        i < v.len(),
    ensures
        v[i] == v[i],
{
    proof {
    }
}

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement array sum using int indices */
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] + b[j],
        decreases
            a.len() - i
    {
        let sum: i32 = a[i] + b[i];
        res.push(sum);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}