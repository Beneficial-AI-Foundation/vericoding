use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper section left intentionally minimal; no extra lemmas required for this task.
// </vc-helpers>

// <vc-spec>
fn element_wise_divide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let mut v: Vec<int> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant v.len() == i;
        invariant forall |j: nat| j < i ==> v@[j] == a[j as int] / b[j as int];
        decreases n - i;
    {
        let ai: int = a[i as int];
        let bi: int = b[i as int];
        v.push(ai / bi);
        i = i + 1;
    }
    let res: Seq<int> = v.into_seq();
    proof {
        assert(res.len() == n);
        assert(forall |ii: int| 0 <= ii && ii < res.len() ==>
            res[ii] == a[ii] / b[ii]);
    }
    res
}
// </vc-code>

fn main() {
}

}