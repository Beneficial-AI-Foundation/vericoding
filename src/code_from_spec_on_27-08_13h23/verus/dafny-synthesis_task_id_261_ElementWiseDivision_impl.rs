use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
{
    let mut res: Vec<int> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|k: int| 0 <= k < i ==> res[k as usize] == a[k] / b[k],
    {
        res.push(a[i] / b[i]);
        i = i + 1;
    }

    res.into()
}
// </vc-code>

fn main() {
}

}