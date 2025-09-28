// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): establish i8 numeric bounds when viewed as int */
proof fn lemma_i8_in_range(v: i8)
    ensures
        -128 <= v as int && v as int <= 127,
{
}

/* helper modified by LLM (iteration 5): order preservation from int comparison to i8 comparison */
proof fn lemma_int_lt_implies_i8_lt(a: i8, b: i8)
    ensures
        (a as int) < (b as int) ==> a < b,
{
}

/* helper modified by LLM (iteration 5): casting i16 to i8 preserves value within i8 range */
proof fn lemma_i16_to_i8_roundtrip_in_range(c: i16)
    requires
        -128 <= c as int, c as int <= 127,
    ensures
        ((c as i8) as int) == c as int,
{
}

// </vc-helpers>

// <vc-spec>
fn union1d(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        /* Union property: every element from either input array is in result */
        forall|i: int| 0 <= i < ar1.len() ==> 
            #[trigger] result@.contains(ar1[i]),
        forall|i: int| 0 <= i < ar2.len() ==> 
            #[trigger] result@.contains(ar2[i]),
        /* Completeness: every element in result comes from one of the input arrays */
        forall|j: int| 0 <= j < result.len() ==> 
            ar1@.contains(result[j]) || ar2@.contains(result[j]),
        /* Sorted property: result is sorted in ascending order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            #[trigger] result[i] <= #[trigger] result[j],
        /* Uniqueness property: no duplicate elements */
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i16 counter to iterate range, avoid int->i8 casts, and maintain invariants for correctness */
    let I8_MIN: i16 = -128i16;
    let I8_MAX: i16 = 127i16;
    let mut res: Vec<i8> = Vec::new();
    let mut cur: i16 = I8_MIN;
    while cur <= I8_MAX
        invariant
            I8_MIN <= cur && cur <= I8_MAX + 1i16,
            forall|x: i8| (x as int) < (cur as int) ==> #[trigger] res@.contains(x) == (ar1@.contains(x) || ar2@.contains(x)),
            forall|k: int| 0 <= k < res.len() ==> ar1@.contains(res[k]) || ar2@.contains(res[k]),
            forall|i: int, j: int| 0 <= i < j < res.len() ==> (res[i] as int) < (res[j] as int),
            forall|k: int| 0 <= k < res.len() ==> (res[k] as int) < (cur as int),
        decreases I8_MAX as int + 1 - cur as int
    {
        if ar1@.contains(cur as i8) || ar2@.contains(cur as i8) {
            res.push(cur as i8);
            proof { lemma_i16_to_i8_roundtrip_in_range(cur); }
        }
        cur = cur + 1i16;
    }
    proof {
        assert(cur == I8_MAX + 1i16);
        assert forall|i: int, j: int| 0 <= i < j < res.len() ==> res[i] <= res[j] by {
            if 0 <= i && i < j && j < res.len() {
                assert((res[i] as int) < (res[j] as int));
                lemma_int_lt_implies_i8_lt(res[i], res[j]);
                assert(res[i] <= res[j]);
            }
        };
        assert forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < res.len() && i != j ==> res[i] != res[j] by {
            if 0 <= i && i < res.len() && 0 <= j && j < res.len() && i != j {
                if i < j {
                    assert((res[i] as int) < (res[j] as int));
                    lemma_int_lt_implies_i8_lt(res[i], res[j]);
                    assert(res[i] != res[j]);
                } else {
                    assert((res[j] as int) < (res[i] as int));
                    lemma_int_lt_implies_i8_lt(res[j], res[i]);
                    assert(res[i] != res[j]);
                }
            }
        };
        assert forall|i: int| 0 <= i < ar1.len() ==> res@.contains(ar1[i]) by {
            if 0 <= i && i < ar1.len() {
                let v = ar1[i];
                lemma_i8_in_range(v);
                assert((v as int) < (cur as int));
                assert(res@.contains(v) == (ar1@.contains(v) || ar2@.contains(v)));
                assert(ar1@.contains(v));
                assert(res@.contains(v));
            }
        };
        assert forall|i: int| 0 <= i < ar2.len() ==> res@.contains(ar2[i]) by {
            if 0 <= i && i < ar2.len() {
                let v = ar2[i];
                lemma_i8_in_range(v);
                assert((v as int) < (cur as int));
                assert(res@.contains(v) == (ar1@.contains(v) || ar2@.contains(v)));
                assert(ar2@.contains(v));
                assert(res@.contains(v));
            }
        };
        assert forall|k: int| 0 <= k < res.len() ==> ar1@.contains(res[k]) || ar2@.contains(res[k]) by {
            if 0 <= k && k < res.len() {
                assert((res[k] as int) < (cur as int));
                assert(res@.contains(res[k]) == (ar1@.contains(res[k]) || ar2@.contains(res[k])));
                assert(res@.contains(res[k]));
            }
        };
    }
    res
} 

// </vc-code>


}
fn main() {}