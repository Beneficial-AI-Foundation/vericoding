// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple max/min helpers and index lemmas */
pub open spec fn max_len(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 5): from j < max_len(a,b) derive j < a or j < b */
pub proof fn lemma_lt_max_implies_lt_one(a: nat, b: nat, j: nat)
    ensures
        j < max_len(a, b) ==> j < a || j < b,
{
    if a >= b {
        assert(max_len(a, b) == a);
        if j < max_len(a, b) {
            assert(j < a);
        }
    } else {
        assert(max_len(a, b) == b);
        if j < max_len(a, b) {
            assert(j < b);
        }
    }
}

/* helper modified by LLM (iteration 5): simple max on usize lengths */
pub open spec fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 5): simple min on usize lengths */
pub open spec fn min_usize(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

/* helper modified by LLM (iteration 5): from j < min_usize(a,b) derive j < a and j < b */
pub proof fn lemma_lt_min_implies_lt_both(a: usize, b: usize, j: usize)
    ensures
        j < min_usize(a, b) ==> j < a && j < b,
{
    if a <= b {
        assert(min_usize(a, b) == a);
        if j < min_usize(a, b) {
            assert(j < a);
            assert(a <= b);
            assert(j < b) by {
                assert(j < a);
                assert(a <= b);
            }
        }
    } else {
        assert(min_usize(a, b) == b);
        if j < min_usize(a, b) {
            assert(j < b);
            assert(b < a);
            assert(j < a) by {
                assert(j < b);
                assert(b < a);
            }
        }
    }
}

/* helper modified by LLM (iteration 5): from j < max_usize and !(j < a) deduce j < b */
pub proof fn lemma_lt_max_usize_and_not_lt_left_implies_lt_right(a: usize, b: usize, j: usize)
    ensures
        j < max_usize(a, b) && !(j < a) ==> j < b,
{
    if a >= b {
        assert(max_usize(a, b) == a);
        // antecedent would imply j < a && !(j < a), contradiction; implication holds
    } else {
        assert(max_usize(a, b) == b);
        if j < max_usize(a, b) && !(j < a) {
            assert(j < b);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn hermsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < c1.len() && 0 <= i < c2.len() ==> 
            result@[i] == c1@[i] - c2@[i],
        c1.len() > c2.len() ==> forall|i: int| 
            c2.len() <= i < c1.len() ==> result@[i] == c1@[i],
        c2.len() > c1.len() ==> forall|i: int| 
            c1.len() <= i < c2.len() ==> result@[i] == -c2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement with three phases (overlap, tail c1, tail c2) using wrapping operations to avoid overflow; maintain precise invariants */
    let l1 = c1.len();
    let l2 = c2.len();
    let n = if l1 >= l2 { l1 } else { l2 };
    let m = if l1 <= l2 { l1 } else { l2 };

    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;

    // Phase 1: process overlap with wrapping subtraction
    while i < m
        invariant
            l1 == c1.len(),
            l2 == c2.len(),
            m == if l1 <= l2 { l1 } else { l2 },
            res.len() == i,
            i <= m,
            forall|j: int| 0 <= j < res.len() ==> 0 <= j < c1.len() && 0 <= j < c2.len() && res@[j] == c1@[j] - c2@[j],
        decreases (m as int) - (i as int)
    {
        let v = c1[i].wrapping_sub(c2[i]);
        res.push(v);
        i = i + 1;
    }

    // Phase 2a: c1 longer tail
    if l1 > l2 {
        while i < l1
            invariant
                l1 == c1.len(),
                l2 == c2.len(),
                m == if l1 <= l2 { l1 } else { l2 },
                res.len() == i,
                i <= l1,
                forall|j: int| 0 <= j < m ==> 0 <= j < c1.len() && 0 <= j < c2.len() && res@[j] == c1@[j] - c2@[j],
                forall|j: int| m <= j < res.len() ==> 0 <= j < c1.len() && res@[j] == c1@[j],
            decreases (l1 as int) - (i as int)
        {
            let v = c1[i];
            res.push(v);
            i = i + 1;
        }
    } else if l2 > l1 {
        // Phase 2b: c2 longer tail
        while i < l2
            invariant
                l1 == c1.len(),
                l2 == c2.len(),
                m == if l1 <= l2 { l1 } else { l2 },
                res.len() == i,
                i <= l2,
                forall|j: int| 0 <= j < m ==> 0 <= j < c1.len() && 0 <= j < c2.len() && res@[j] == c1@[j] - c2@[j],
                forall|j: int| m <= j < res.len() ==> 0 <= j < c2.len() && res@[j] == -c2@[j],
            decreases (l2 as int) - (i as int)
        {
            let v = (0i8).wrapping_sub(c2[i]);
            res.push(v);
            i = i + 1;
        }
    }

    // At this point, i == res.len() == n
    res
}
// </vc-code>


}
fn main() {}