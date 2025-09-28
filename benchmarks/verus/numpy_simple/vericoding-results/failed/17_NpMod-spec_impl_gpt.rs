// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix int/usize indexing and return spec-indexed nonzero fact */
proof fn lemma_index_nonzero_from_all_nonzero(v: &Vec<i32>, i: usize)
    requires
        all_nonzero(v@),
        i < v.len(),
    ensures
        v[(i as int)] != 0,
{
    assert(0 <= (i as int));
    assert(v@.len() == v.len() as int);
    assert((i as int) < v@.len());
    assert(all_nonzero(v@));
    assert(v@[(i as int)] != 0);
    assert(v[(i as int)] == v@[(i as int)]);
}
// </vc-helpers>

// <vc-spec>
spec fn all_nonzero(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn mod_vec(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        all_nonzero(b@),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix int/usize index usage in proofs, prove divisor nonzero before modulo, and maintain loop invariant */
    let n: usize = a.len();
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result_vec.len() == i,
            i <= n,
            a.len() == n,
            b.len() == n,
            all_nonzero(b@),
            forall|j: int|
                0 <= j < i as int ==> result_vec@[j] == a@[j] % b@[j],
        decreases n - i
    {
        let ai: i32 = a[i];
        let bi: i32 = b[i];
        proof {
            assert(ai == a[(i as int)]);
            assert(bi == b[(i as int)]);
            lemma_index_nonzero_from_all_nonzero(&b, i);
            assert(b[(i as int)] != 0);
            assert(bi != 0);
        }
        let rem: i32 = ai % bi;
        let old_view = result_vec@;
        result_vec.push(rem);
        proof {
            assert(result_vec@ == old_view.push(rem));
            assert forall|j: int|
                0 <= j < (i + 1) as int ==> result_vec@[j] == a@[j] % b@[j]
            by {
                if j < i as int {
                    assert(0 <= j);
                    assert(j < old_view.len() as int);
                    assert(result_vec@[j] == old_view.push(rem)[j]);
                    assert(old_view.push(rem)[j] == old_view[j]);
                    assert(old_view[j] == a@[j] % b@[j]);
                } else {
                    assert(old_view.len() as int == i as int);
                    assert(!(j < i as int));
                    assert(j < (i + 1) as int);
                    assert(j == i as int);
                    assert(result_vec@[j] == old_view.push(rem)[j]);
                    assert(old_view.push(rem)[j] == rem);
                    assert(ai == a[(i as int)]);
                    assert(bi == b[(i as int)]);
                    assert(a[(i as int)] == a@[(i as int)]);
                    assert(b[(i as int)] == b@[(i as int)]);
                    assert(rem == ai % bi);
                    assert(rem == a@[(i as int)] % b@[(i as int)]);
                    assert(rem == a@[j] % b@[j]);
                }
            }
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}