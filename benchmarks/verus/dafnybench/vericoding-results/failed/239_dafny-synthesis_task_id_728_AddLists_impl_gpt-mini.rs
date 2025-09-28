use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn add_lists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let result: Seq<int> = Seq::new(n, |i: int| -> int { a[i] + b[i] });
    proof {
        assert(result.len() == n);
        assert(forall |k: int| 0 <= k && k < result.len() ==>
            result[k] == a[k] + b[k]
        );
    }
    result
}
// </vc-code>

fn main() {}

}