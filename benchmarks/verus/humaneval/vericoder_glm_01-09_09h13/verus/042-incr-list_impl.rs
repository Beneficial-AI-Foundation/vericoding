use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_incr_list_precondition(l: Vec<i32>, i: usize)
    requires
        forall|j: int| 0 <= j < l.len() ==> l[j] + 1 <= i32::MAX,
        0 <= i < l.len(),
    ensures
        l[i] + 1 <= i32::MAX,
{
    assert(l[i] == l[i as int]);
    assert(l[i as int] + 1 <= i32::MAX);
}
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
    for i in 0..l.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] result[j] == l[j] + 1
    {
        lemma_incr_list_precondition(l, i);
        result.push(l[i] + 1);
    }
    result
}
// </vc-code>

fn main() {}
}