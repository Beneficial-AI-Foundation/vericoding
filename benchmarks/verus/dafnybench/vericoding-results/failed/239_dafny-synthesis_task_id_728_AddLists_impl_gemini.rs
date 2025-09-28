// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

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
    /* code modified by LLM (iteration 5): Fixed type mismatches for nat and corrected sequence indexing syntax. */
    let mut result: Seq<int> = Seq::empty();
    let mut i: nat = 0 as nat;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] + b[j],
        decreases a.len() - i
    {
        result = result.push(a[i] + b[i]);
        i = i + 1 as nat;
    }
    result
}
// </vc-code>

}
fn main() {}