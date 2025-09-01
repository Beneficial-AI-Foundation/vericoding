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
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    let n: nat = l.len();
    while i < n
        invariant i <= n;
        invariant res.len() == i;
        invariant forall|j: nat| j < i ==> res[j] == l[j] + 1;
    {
        // safe by precondition: for this i, l[i] + 1 <= i32::MAX
        res.push(l[i] + 1);
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert(res.len() == n);
        assert(forall|k: nat| k < n ==> res[k] == l[k] + 1);
        assert(forall|k: int| 0 <= k && k < l.len() as int ==>
            res[k as nat] == l[k as nat] + 1);
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}