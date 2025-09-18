// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant import. */
pub open spec fn merge(a: Seq<i32>, b: Seq<i32>) -> Seq<i32>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]].add(merge(a.skip(1), b))
    } else {
        seq![b[0]].add(merge(a, b.skip(1)))
    }
}

proof fn merge_is_sorted(a: Seq<i32>, b: Seq<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] <= b[j]
    ensures forall|i: int, j: int| 0 <= i < j < merge(a, b).len() ==> merge(a, b)[i] <= merge(a, b)[j]
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        assert(forall|i: int, j: int| 0 <= i < j < merge(a, b).len() ==> merge(a, b)[i] <= merge(a, b)[j]);
    } else if b.len() == 0 {
        assert(forall|i: int, j: int| 0 <= i < j < merge(a, b).len() ==> merge(a, b)[i] <= merge(a, b)[j]);
    } else if a[0] <= b[0] {
        merge_is_sorted(a.skip(1), b);
        assert(merge(a, b)[0] == a[0]);
        assert(forall|i: int, j: int| 0 <= i < j < merge(a.skip(1), b).len() ==> merge(a.skip(1), b)[i] <= merge(a.skip(1), b)[j]);

        assert(merge(a, b).len() == 1 + (a.skip(1).len() + b.len()));
        if 1 < merge(a, b).len() {
            assert(merge(a, b)[0] <= merge(a, b)[1]);
        }
    } else {
        merge_is_sorted(a, b.skip(1));
        assert(merge(a, b)[0] == b[0]);
        assert(forall|i: int, j: int| 0 <= i < j < merge(a, b.skip(1)).len() ==> merge(a, b.skip(1))[i] <= merge(a, b.skip(1))[j]);

        assert(merge(a, b).len() == 1 + (a.len() + b.skip(1).len()));
        if 1 < merge(a, b).len() {
            assert(merge(a, b)[0] <= merge(a, b)[1]);
        }
    }
    assert(forall|i: int, j: int| 0 <= i < j < merge(a, b).len() ==> merge(a, b)[i] <= merge(a, b)[j]);
}

proof fn merge_preserves_length(a: Seq<i32>, b: Seq<i32>)
    ensures merge(a, b).len() == a.len() + b.len()
    decreases a.len() + b.len()
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        merge_preserves_length(a.skip(1), b);
    } else {
        merge_preserves_length(a, b.skip(1));
    }
}

proof fn merge_preserves_multiset(a: Seq<i32>, b: Seq<i32>)
    ensures merge(a, b).to_multiset() =~= a.to_multiset() + b.to_multiset()
    decreases a.len() + b.len()
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] <= b[0] {
        merge_preserves_multiset(a.skip(1), b);
        assert(merge(a.skip(1), b).to_multiset() =~= a.skip(1).to_multiset() + b.to_multiset());
        assert(merge(a, b).to_multiset() =~= (seq![a[0]].add(merge(a.skip(1), b))).to_multiset());
        assert(merge(a, b).to_multiset() =~= seq![a[0]].to_multiset() + merge(a.skip(1), b).to_multiset());
    } else {
        merge_preserves_multiset(a, b.skip(1));
        assert(merge(a, b.skip(1)).to_multiset() =~= a.to_multiset() + b.skip(1).to_multiset());
        assert(merge(a, b).to_multiset() =~= (seq![b[0]].add(merge(a, b.skip(1)))).to_multiset());
        assert(merge(a, b).to_multiset() =~= seq![b[0]].to_multiset() + merge(a, b.skip(1)).to_multiset());
    }
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by replacing `multiset![...]` with `seq![...].to_multiset()` for `Seq` operations. */
{
    let len_nat: nat = a.len();
    if len_nat <= 1 {
        a
    } else {
        let mid_nat: nat = len_nat / 2;

        let left_vec = a.subslice(0, mid_nat);
        let right_vec = a.subslice(mid_nat, len_nat - mid_nat);

        let left_sorted = msort(left_vec);
        let right_sorted = msort(right_vec);

        let res_merge = merge(left_sorted@, right_sorted@);

        proof {
            merge_preserves_length(left_sorted@, right_sorted@);
            merge_is_sorted(left_sorted@, right_sorted@);
            merge_preserves_multiset(left_sorted@, right_sorted@);
        }

        res_merge.to_vec_()
    }
}
// </vc-code>

}
fn main() {}