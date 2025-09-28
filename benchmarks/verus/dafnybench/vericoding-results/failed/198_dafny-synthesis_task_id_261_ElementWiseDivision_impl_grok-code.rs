use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::empty();
    let mut i: int = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall |j: int| j < i ==> #[trigger] result[j] == a[j] / b[j]
    {
        result = result.push(a[i] / b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}