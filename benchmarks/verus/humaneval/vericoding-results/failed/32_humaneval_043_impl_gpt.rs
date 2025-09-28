// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): witness lemma for the existential property */
proof fn lemma_witness_has_pair(s: Seq<int>, i: int, j: int)
    requires
        0 <= i,
        i < j,
        j < s.len(),
        s[i] + s[j] == 0,
    ensures
        has_pair_sum_to_zero(s),
{
    assert(exists|p: int, q: int| 0 <= p < q < s.len() && s[p] + s[q] == 0) by {
        assert(0 <= i < j < s.len() && s[i] + s[j] == 0);
    }
}

/* helper modified by LLM (iteration 5): lemma for the negation of the existential when all pairs are non-zero */
proof fn lemma_no_pair_implies_not_exists(s: Seq<int>)
    requires
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] + s[q] != 0,
    ensures
        !has_pair_sum_to_zero(s),
{
    assert(!(exists|i: int, j: int| 0 <= i < j < s.len() && s[i] + s[j] == 0)) by {
        if exists|i: int, j: int| 0 <= i < j < s.len() && s[i] + s[j] == 0 {
            let (i, j) = choose|i: int, j: int| 0 <= i < j < s.len() && s[i] + s[j] == 0;
            assert(0 <= i < j < s.len());
            assert(s[i] + s[j] == 0);
            assert(s[i] + s[j] != 0);
            assert(false);
        }
    }
}

/* helper modified by LLM (iteration 5): relate map(|i,x| x as int) indexing with original sequence indexing */
proof fn lemma_map_index_cast(v: Seq<i8>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v.map(|k: int, x: i8| x as int)[i] == v[i] as int,
{
    assert(v.map(|k: int, x: i8| x as int)[i] == (|k: int, x: i8| x as int)(i, v[i]));
    assert((|k: int, x: i8| x as int)(i, v[i]) == v[i] as int);
}

/* helper modified by LLM (iteration 5): bridge zero-sum between i32 exec arithmetic and spec int arithmetic for i8 values */
proof fn lemma_sum_zero_i32_int(a: i8, b: i8)
    ensures
        ((a as i32) + (b as i32) == 0) ==> ((a as int) + (b as int) == 0),
        ((a as int) + (b as int) == 0) ==> ((a as i32) + (b as i32) == 0),
{
    if ((a as i32) + (b as i32) == 0) {
        assert((((a as i32) + (b as i32)) as int) == 0);
        assert(((a as i32) as int) == (a as int));
        assert(((b as i32) as int) == (b as int));
        assert((((a as i32) + (b as i32)) as int) == ((a as int) + (b as int)));
        assert((a as int) + (b as int) == 0);
    }
    if ((a as int) + (b as int) == 0) {
        assert(((a as i32) as int) == (a as int));
        assert(((b as i32) as int) == (b as int));
        assert((((a as i32) + (b as i32)) as int) == ((a as int) + (b as int)));
        assert((((a as i32) + (b as i32)) as int) == 0);
        assert((0i32 as int) == 0);
        assert((((a as i32) + (b as i32)) as int) == (0i32 as int));
        assert(((a as i32) + (b as i32)) == 0i32);
    }
}
// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix chained comparison with casts and strengthen bounds/bridging steps */
    let n = l.len();
    let ghost s = l@.map(|i: int, x: i8| x as int);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|p: int, q: int| 0 <= p < q < i as int ==> s[p] + s[q] != 0,
        decreases n - i
    {
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                i <= n,
                forall|p: int, q: int| 0 <= p < q < i as int ==> s[p] + s[q] != 0,
                forall|p: int| 0 <= p < j as int ==> s[p] + s[i as int] != 0,
            decreases i - j
        {
            let sum: i32 = (l[j] as i32) + (l[i] as i32);
            if sum == 0 {
                proof {
                    assert(i < n);
                    assert(j < i);
                    assert(j < n);
                    assert(0 <= j as int && j as int < n as int);
                    assert(0 <= i as int && i as int < n as int);
                    // Relate s and l at indices j and i
                    lemma_map_index_cast(l@, j as int);
                    lemma_map_index_cast(l@, i as int);
                    assert(s[j as int] == l@[j as int] as int);
                    assert(s[i as int] == l@[i as int] as int);
                    assert(l@[j as int] == l[j]);
                    assert(l@[i as int] == l[i]);
                    // Bridge equality from i32 sum to int sum
                    assert(sum == (l[j] as i32) + (l[i] as i32));
                    lemma_sum_zero_i32_int(l[j], l[i]);
                    assert((l[j] as int) + (l[i] as int) == 0);
                    assert(s[j as int] + s[i as int] == 0);
                    // Bounds for witness
                    assert(s.len() == l@.len());
                    assert(l@.len() == n as int);
                    assert(0 <= j as int && j as int < i as int);
                    assert(i as int < s.len());
                    // Existential witness
                    lemma_witness_has_pair(s, j as int, i as int);
                }
                return true;
            } else {
                proof {
                    // Maintain invariant for the new j by showing s[j] + s[i] != 0
                    assert(i < n);
                    assert(j < i);
                    assert(0 <= j as int && j as int < n as int);
                    assert(0 <= i as int && i as int < n as int);
                    lemma_map_index_cast(l@, j as int);
                    lemma_map_index_cast(l@, i as int);
                    assert(s[j as int] == l@[j as int] as int);
                    assert(s[i as int] == l@[i as int] as int);
                    assert(l@[j as int] == l[j]);
                    assert(l@[i as int] == l[i]);
                    lemma_sum_zero_i32_int(l[j], l[i]);
                    assert(sum == (l[j] as i32) + (l[i] as i32));
                    assert(!(((l[j] as int) + (l[i] as int) == 0))) by {
                        if ( (l[j] as int) + (l[i] as int) == 0 ) {
                            assert(((l[j] as i32) + (l[i] as i32)) == 0);
                            assert(false);
                        }
                    }
                    assert(s[j as int] + s[i as int] != 0);
                }
                j += 1;
            }
        }
        i += 1;
    }
    proof {
        assert(i == n);
        assert(s.len() == l@.len());
        assert(l@.len() == n as int);
        // From the outer invariant with i == n, all pairs are non-zero
        lemma_no_pair_implies_not_exists(s);
    }
    false
}
// </vc-code>


}

fn main() {}