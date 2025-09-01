use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == l@[j] + 1,
            forall|j: int| 0 <= j < l.len() ==> l@[j] + 1 <= i32::MAX,
        decreases l.len() - i,
    {
        let val = l[i as int];
        assert(val + 1 <= i32::MAX);  // Use the precondition through the invariant
        result.push(val + 1);
        
        assert(result.len() == i + 1);
        assert(result@[i as int] == l@[i as int] + 1);
        assert(forall|j: int| 0 <= j < i ==> result@[j] == l@[j] + 1);
        
        i = i + 1;
    }
    
    result
    // impl-end
}
// </vc-code>

fn main() {}
}