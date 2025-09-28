use vstd::prelude::*;

verus! {

// <vc-helpers>
fn add_seq_element_at_index(a: Seq<int>, b: Seq<int>, idx: int) -> int
    requires
        0 <= idx < a.len(),
        a.len() == b.len(),
    ensures
        add_seq_element_at_index(a, b, idx) == a[idx] + b[idx],
{
    a[idx] + b[idx]
}
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
    let len = a.len();
    let mut result_vec: Vec<int> = Vec::new();
    let mut i: nat = 0;

    while i < len
        invariant
            i <= len,
            result_vec.len() == i,
            result_vec.capacity() == len,
            forall|j: int| 0 <= j < i ==> result_vec@[j] == a[j] + b[j],
    {
        // Cast i to int for the function call argument.
        let element_to_add = add_seq_element_at_index(a, b, i as int); 
        result_vec.push(element_to_add);
        i = i + 1;
    }
    
    proof {
        assert(result_vec.len() == len);
    }
    result_vec.to_seq()
}
// </vc-code>

fn main() {}

}