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
    let n = l.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n {
        invariant (result.len() == i && (forall |j: usize| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1));
        result.push(l[i] + 1);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}