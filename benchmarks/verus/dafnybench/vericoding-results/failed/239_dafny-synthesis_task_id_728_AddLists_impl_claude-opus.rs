use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut result: Vec<int> = Vec::new();
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a[j] + b[j],
    {
        let sum = a[i as int] + b[i as int];
        result.push(sum);
        
        assert(result@.len() == i + 1);
        assert(result@[i as int] == a[i as int] + b[i as int]);
        
        i = i + 1;
    }
    
    assert(result@.len() == n);
    assert(forall|j: int| 0 <= j < n ==> result@[j] == a[j] + b[j]);
    
    result@
}
// </vc-code>

fn main() {}

}