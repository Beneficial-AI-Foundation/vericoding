use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added helper to instantiate the int-indexed precondition for nat indices.
fn precond_index(l: &Vec<i32>, k: nat)
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
        k < l.len(),
    ensures
        l[k as int] + 1 <= i32::MAX,
{
    proof {
        let i: int = k as int;
        assert(0 <= i && i < l.len());
        assert(l[i] + 1 <= i32::MAX);
    }
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
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < l.len()
        invariant i <= l.len();
        invariant res.len() == i;
        invariant forall|k: nat| k < i ==> #[trigger] res[k as int] == l[k as int] + 1;
        decreases l.len() - i;
    {
        // instantiate precondition for this index
        precond_index(&l, i);

        let v: i32 = l[i as int] + 1;
        res.push(v);
        i = i + 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}