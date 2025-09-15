// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_matches(xs: Seq<u64>, x: u64) -> nat
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let first_match: nat = if xs[0] == x { 1 } else { 0 };
        first_match + count_matches(xs.skip(1), x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): witness for majority element in a sequence */
spec fn witness_majority_seq(xs: Seq<u64>) -> u64
    requires exists |x: u64| count_matches(xs, x) > xs.len()/2
    ensures count_matches(xs, result) > xs.len()/2
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let head = xs@[0];
        if count_matches(xs, head) > xs.len()/2 {
            head
        } else {
            witness_majority_seq(xs.skip(1))
        }
    }
}

/* helper modified by LLM (iteration 5): proof that positive count implies an index exists */
proof fn exists_index_of_match(xs: Seq<u64>, w: u64)
    ensures count_matches(xs, w) > 0 ==> (exists |j: usize| j < xs.len() && xs@[j] == w)
    decreases xs.len()
{
    if xs.len() == 0 {
        // vacuously true since count_matches(xs,w) == 0
    } else {
        if xs@[0] == w {
            proof {
                // witness is 0
                assert(count_matches(xs, w) > 0 ==> exists |j: usize| j < xs.len() && xs@[j] == w);
                assert(xs@[0] == w);
                assert(exists |j: usize| j < xs.len() && xs@[j] == w);
            }
        } else {
            proof {
                // xs@[0] != w, so count_matches(xs, w) == count_matches(xs.skip(1), w)
                assert((if xs@[0] == w { 1 } else { 0 }) + count_matches(xs.skip(1), w) > 0 ==> count_matches(xs.skip(1), w) > 0);
                exists_index_of_match(xs.skip(1), w);
                let j = choose |j: usize| j < xs.skip(1).len() && xs.skip(1)@[j] == w;
                assert(j < xs.skip(1).len());
                assert(xs.skip(1)@[j] == w);
                assert(j + 1 < xs.len());
                assert(xs@[j + 1] == w);
                assert(exists |j0: usize| j0 < xs.len() && xs@[j0] == w);
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn majority_element(xs: &Vec<u64>) -> (result: u64)
    requires 
        xs.len() > 0,
        exists|x: u64| count_matches(xs@, x) > xs.len() / 2,
    ensures
        count_matches(xs@, result) > xs.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): find spec witness and return an index with that value */
    let n = xs.len();
    let w: u64 = witness_majority_seq(xs@);
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        invariant forall |k: usize| k < i ==> xs@[k] != w,
        decreases n - i
    {
        if xs[i] == w {
            break;
        }
        i = i + 1;
    }
    proof {
        // there must exist an index with value w
        assert(count_matches(xs@, w) > 0);
        exists_index_of_match(xs@, w);
        let j = choose |j: usize| j < n && xs@[j] == w;
        assert(j < n);
        assert(xs@[j] == w);
        assert(forall |k: usize| k < i ==> xs@[k] != w);
        // if j < i then xs@[j] != w, contradiction with xs@[j] == w
        assert(j < i ==> xs@[j] != w);
        assert(!(j < i));
        assert(j >= i);
        assert(i < n);
    }
    xs[i]
}

// </vc-code>

}
fn main() {}