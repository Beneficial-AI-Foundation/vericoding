use vstd::prelude::*;

verus! {

// verifies
// check that string between indexes low and high-1 are sorted
spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

// <vc-helpers>
proof fn lemma_sorted3_from_pairwise(s: Seq<char>)
    requires
        s.len() == 3,
        s[0] <= s[1],
        s[1] <= s[2],
    ensures
        sorted(s, 0, 3),
{
    assert_forall_by(|j: int, k: int| {
        requires 0 <= j < k < 3;
        ensures s[j] <= s[k];

        if j == 0 && k == 1 {
            assert(s[0] <= s[1]);
        } else if j == 0 && k == 2 {
            assert(s[0] <= s[1]);
            assert(s[1] <= s[2]);
            assert(s[0] <= s[2]);
        } else {
            assert(j == 1 && k == 2);
            assert(s[1] <= s[2]);
        }
    });
}
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    let x0 = a[0];
    let x1 = a[1];
    let x2 = a[2];

    if x0 <= x1 {
        if x1 <= x2 {
            // x0 <= x1 <= x2
            let bb = seq![x0, x1, x2];
            assert(bb.len() == 3);
            assert(x0 <= x1);
            assert(x1 <= x2);
            lemma_sorted3_from_pairwise(bb);
            assert(sorted(bb, 0, bb.len() as int));
            assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
            return bb;
        } else {
            // x2 < x1
            if x0 <= x2 {
                // x0 <= x2 < x1
                let bb = seq![x0, x2, x1];
                assert(bb.len() == 3);
                assert(x0 <= x2);
                assert(x2 <= x1);
                lemma_sorted3_from_pairwise(bb);
                assert(sorted(bb, 0, bb.len() as int));
                assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
                return bb;
            } else {
                // x2 < x0 <= x1
                let bb = seq![x2, x0, x1];
                assert(bb.len() == 3);
                assert(x2 <= x0);
                assert(x0 <= x1);
                lemma_sorted3_from_pairwise(bb);
                assert(sorted(bb, 0, bb.len() as int));
                assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
                return bb;
            }
        }
    } else {
        // x1 < x0
        if x0 <= x2 {
            // x1 < x0 <= x2
            let bb = seq![x1, x0, x2];
            assert(bb.len() == 3);
            assert(x1 <= x0);
            assert(x0 <= x2);
            lemma_sorted3_from_pairwise(bb);
            assert(sorted(bb, 0, bb.len() as int));
            assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
            return bb;
        } else {
            // x2 < x0
            if x1 <= x2 {
                // x1 <= x2 < x0
                let bb = seq![x1, x2, x0];
                assert(bb.len() == 3);
                assert(x1 <= x2);
                assert(x2 <= x0);
                lemma_sorted3_from_pairwise(bb);
                assert(sorted(bb, 0, bb.len() as int));
                assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
                return bb;
            } else {
                // x2 < x1 < x0
                let bb = seq![x2, x1, x0];
                assert(bb.len() == 3);
                assert(x2 <= x1);
                assert(x1 <= x0);
                lemma_sorted3_from_pairwise(bb);
                assert(sorted(bb, 0, bb.len() as int));
                assert(seq![bb[0], bb[1], bb[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset());
                return bb;
            }
        }
    }
}
// </vc-code>

fn main() {
}

}