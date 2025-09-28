use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<int> = Vec::new();
    let n: nat = a.len();
    let mut i: nat = 0;
    while i < n
        invariant i <= n
        invariant v.len() == i
        invariant forall |j: nat| #[trigger] j < i ==> v.as_seq()[(j as int)] == a[(j as int)] / b[(j as int)]
    {
        proof {
            assert((i as int) >= 0);
            assert((i as int) < (b.len() as int));
            assert(b[(i as int)] != 0);
        }
        let val = a[(i as int)] / b[(i as int)];
        v.push(val);
        i += 1;
    }
    let res = v.into_seq();
    proof {
        assert(res.len() == n);
        assert(forall |j: nat| #[trigger] j < n ==> res[(j as int)] == a[(j as int)] / b[(j as int)]);
        assert(forall |k: int| #[trigger] 0 <= k && k < (res.len() as int) ==> res[k] == a[k] / b[k]);
    }
    res
}
// </vc-code>

fn main() {
}

}