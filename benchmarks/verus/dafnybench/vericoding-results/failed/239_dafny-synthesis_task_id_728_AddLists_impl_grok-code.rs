use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add_lists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Seq<int> = Seq::<int>::empty();
    let mut i: nat = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: nat| j < i ==> result[j] == a[j] + b[j],
            decreases a.len() - i
    {
        result = result.push(a[i] + b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}