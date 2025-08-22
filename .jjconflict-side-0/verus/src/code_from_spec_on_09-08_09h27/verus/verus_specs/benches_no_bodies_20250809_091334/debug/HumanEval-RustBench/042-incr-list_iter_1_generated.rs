use vstd::prelude::*;

verus! {

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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < l.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == l[j] + 1,
    {
        result.push(l[i] + 1);
        i += 1;
    }
    
    result
}

}
fn main() {}