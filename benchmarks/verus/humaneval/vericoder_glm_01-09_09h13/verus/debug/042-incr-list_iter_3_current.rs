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
    let mut result = Vec::new();
    let len = l.len() as int;
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1
    {
        result.push(l[i] + 1);
    }
    result
}
// </vc-code>

fn main() {}
}