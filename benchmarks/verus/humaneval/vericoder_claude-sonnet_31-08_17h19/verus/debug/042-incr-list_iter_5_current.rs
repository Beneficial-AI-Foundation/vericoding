use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == l@[j] + 1,
        decreases l.len() - i,
    {
        let incremented = l@[i as int] + 1;
        result.push(incremented);
        i += 1;
        
        assert(forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == l@[j] + 1);
    }
    
    result
    // impl-end
}
// </vc-code>

fn main() {}
}