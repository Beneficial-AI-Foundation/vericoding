// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): keep simple max/min helpers and a small lemma about max */
pub open spec fn max_usize(a: usize, b: usize) -> usize { if a >= b { a } else { b } }

/* helper modified by LLM (iteration 5): keep simple max/min helpers and a small lemma about max */
pub open spec fn min_usize(a: usize, b: usize) -> usize { if a <= b { a } else { b } }

/* helper modified by LLM (iteration 5): lemma relating i < max(a,b) to i < a or i < b */
pub proof fn max_implies_one_side(a: usize, b: usize, i: int)
    ensures
        0 <= i < max_usize(a, b) ==> i < a || i < b,
{
    if a >= b {
        assert((0 <= i && i < a) ==> i < a);
    } else {
        assert((0 <= i && i < b) ==> i < b);
    }
}

// </vc-helpers>

// <vc-spec>
fn polysub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int - c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] == c1[i]
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == 0 - c2[i] as int
            } else {
                result[i] == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): strengthen loop invariants for safe indexing and content relations; add finalization loops */
    let len1 = c1.len();
    let len2 = c2.len();

    if len1 >= len2 {
        let n = len1;
        let m = len2;
        let mut result: Vec<i8> = c1.clone();

        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i as int <= m as int,
                m <= len2,
                m <= len1,
                result.len() == n,
                forall|k: int| 0 <= k < i as int ==> result[k] as int == c1[k] as int - c2[k] as int,
            decreases (m as int - i as int)
        {
            assert(i < len1);
            assert(i < len2);
            let a = c1[i];
            let b = c2[i];
            let d16: i16 = (a as i16) - (b as i16);
            let d: i8 = #[verifier::truncate] (d16 as i8);
            // establish property for index i for next iteration
            proof {
                assert(((a as i16) as int) == (a as int));
                assert(((b as i16) as int) == (b as int));
                assert((d16 as int) == ((a as i16) as int - (b as i16) as int));
                assert((d as int) == (d16 as int));
                assert((d as int) == (a as int) - (b as int));
            }
            assert(i < result.len());
            result.set(i, d);
            i = i + 1;
        }

        // Fill remaining indices with c1 values explicitly to ease reasoning
        let mut j: usize = m;
        while j < len1
            invariant
                m as int <= j as int <= len1 as int,
                result.len() == n,
                forall|k: int| 0 <= k < m as int ==> result[k] as int == c1[k] as int - c2[k] as int,
                forall|k: int| m as int <= k < j as int ==> result[k] == c1[k],
            decreases (len1 as int - j as int)
        {
            assert(j < len1);
            let cj = c1[j];
            assert(j < result.len());
            result.set(j, cj);
            j = j + 1;
        }

        result
    } else {
        let n = len2;
        let m = len1;
        let mut result: Vec<i8> = c2.clone();

        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i as int <= m as int,
                m <= len1,
                m <= len2,
                result.len() == n,
                forall|k: int| 0 <= k < i as int ==> result[k] as int == c1[k] as int - c2[k] as int,
            decreases (m as int - i as int)
        {
            assert(i < len1);
            assert(i < len2);
            let a = c1[i];
            let b = c2[i];
            let d16: i16 = (a as i16) - (b as i16);
            let d: i8 = #[verifier::truncate] (d16 as i8);
            proof {
                assert(((a as i16) as int) == (a as int));
                assert(((b as i16) as int) == (b as int));
                assert((d16 as int) == ((a as i16) as int - (b as i16) as int));
                assert((d as int) == (d16 as int));
                assert((d as int) == (a as int) - (b as int));
            }
            assert(i < result.len());
            result.set(i, d);
            i = i + 1;
        }

        let mut j: usize = len1;
        while j < len2
            invariant
                0 <= m as int <= len1 as int,
                len1 as int <= j as int <= len2 as int,
                result.len() == n,
                forall|k: int| 0 <= k < m as int ==> result[k] as int == c1[k] as int - c2[k] as int,
                forall|k: int| m as int <= k < j as int ==> result[k] as int == 0 - c2[k] as int,
            decreases (len2 as int - j as int)
        {
            assert(j < len2);
            let cj = c2[j];
            let v16: i16 = 0i16 - (cj as i16);
            let v: i8 = #[verifier::truncate] (v16 as i8);
            proof {
                assert(((cj as i16) as int) == (cj as int));
                assert((v16 as int) == 0 - (cj as int));
                assert((v as int) == (v16 as int));
                assert((v as int) == 0 - (cj as int));
            }
            assert(j < result.len());
            result.set(j, v);
            j = j + 1;
        }

        result
    }
}
// </vc-code>


}
fn main() {}