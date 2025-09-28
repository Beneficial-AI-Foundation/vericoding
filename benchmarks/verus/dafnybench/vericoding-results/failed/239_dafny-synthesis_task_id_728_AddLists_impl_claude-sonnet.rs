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
    let mut result = Seq::<int>::empty();
    let mut i: nat = 0nat;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] + b[j],
    {
        proof {
            let sum = a[i as int] + b[i as int];
        }
        result = result.push(a[i as int] + b[i as int]);
        i = i + 1nat;
    }
    
    result
}
// </vc-code>

fn main() {}

}