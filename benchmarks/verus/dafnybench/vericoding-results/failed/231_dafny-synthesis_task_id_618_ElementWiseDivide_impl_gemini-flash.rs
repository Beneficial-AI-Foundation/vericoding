use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_divide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    let n = a.len();

    // Preserve the original sequences for the loop invariant
    let a_seq = a;
    let b_seq = b;

    let mut i: nat = 0;
    while (i < n)
        invariant 
            i <= n,
            result.len() == i,
            result.content_deep_equal(Seq::new().push_slice(a_seq.subsequence(0, i as int).map(|k: int, x: int| x / b_seq.index(k)))),
            a_seq.len() == n,
            b_seq.len() == n,
            forall|k: int| 0 <= k < b_seq.len() ==> b_seq.index(k) != 0,
    {
        result.push(a_seq.index(i as int) / b_seq.index(i as int));
        i = (i + 1) as nat;
    }

    result
}
// </vc-code>

fn main() {
}

}