use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: nat = l.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < n {
        invariant i <= n;
        invariant result.len() == i;
        invariant forall|j: nat| j < i ==> #[trigger] result[j] == l[j] + 1;
        decreases n - i;
        let v: i32 = l[i];
        result.push(v + 1);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}