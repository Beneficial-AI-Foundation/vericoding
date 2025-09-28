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
    let n = a.len();
    let mut result_vec = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[j] == a[j] / b[j],
    {
        result_vec.push(a[i] / b[i]);
        i = i + 1;
    }
    result_vec.to_seq()
}
// </vc-code>

fn main() {
}

}