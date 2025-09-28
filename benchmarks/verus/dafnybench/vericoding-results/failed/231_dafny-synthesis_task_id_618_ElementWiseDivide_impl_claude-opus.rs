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
    let mut result: Vec<int> = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a[j] / b[j],
    {
        let quotient = a[i as int] / b[i as int];
        result.push(quotient);
        i = i + 1;
    }
    
    result@
}
// </vc-code>

fn main() {
}

}