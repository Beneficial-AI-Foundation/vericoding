// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemmas about u8 bitwise-and properties used in the loop invariants */
pub proof fn lemma_bitand_le_left_u8(a: u8, b: u8)
    ensures
        (a & b) <= a,
{
}

pub proof fn lemma_bitand_le_right_u8(a: u8, b: u8)
    ensures
        (a & b) <= b,
{
}

pub proof fn lemma_bitand_eq_self_when_equal_u8(a: u8, b: u8)
    ensures
        a == b ==> (a & b) == a,
{
}
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] as int >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] as int >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x1[i] as int,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x2[i] as int,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix 'implies' to '==>' and call helper lemmas for bitand properties */
    let n: usize = x1.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() as int == i as int,
            x1.len() == n,
            x2.len() == n,
            0 <= i as int,
            i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> out[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i as int ==> out[j] as int >= 0,
            forall|j: int| 0 <= j < i as int ==> out[j] as int <= x1[j] as int,
            forall|j: int| 0 <= j < i as int ==> out[j] as int <= x2[j] as int,
            forall|j: int| 0 <= j < i as int ==> (x1[j] == x2[j] ==> out[j] == x1[j]),
        decreases (n as int) - (i as int)
    {
        let v: u8 = x1[i] & x2[i];
        out.push(v);
        let old_i: usize = i;
        i = i + 1;
        proof {
            assert(old_i as int + 1 == i as int);

            assert forall|j: int| 0 <= j < i as int ==> out[j] == (x1[j] & x2[j]) by {
                assert(0 <= j && j < i as int);
                if j < old_i as int {
                    // preserved from previous iteration
                } else {
                    assert(j >= old_i as int);
                    assert(j < old_i as int + 1);
                    assert(j == old_i as int);
                    assert(out[old_i as int] == v);
                    assert(v == (x1[old_i as int] & x2[old_i as int]));
                }
            };

            assert forall|j: int| 0 <= j < i as int ==> out[j] as int >= 0 by {
                assert(0 <= j && j < i as int);
                if j < old_i as int {
                    // preserved
                } else {
                    assert(j == old_i as int);
                    // u8 cast to int is always non-negative
                }
            };

            assert forall|j: int| 0 <= j < i as int ==> out[j] as int <= x1[j] as int by {
                assert(0 <= j && j < i as int);
                if j < old_i as int {
                    // preserved
                } else {
                    assert(j == old_i as int);
                    lemma_bitand_le_left_u8(x1[old_i], x2[old_i]);
                    assert(v <= x1[old_i]);
                    assert((v as int) <= (x1[old_i] as int));
                }
            };

            assert forall|j: int| 0 <= j < i as int ==> out[j] as int <= x2[j] as int by {
                assert(0 <= j && j < i as int);
                if j < old_i as int {
                    // preserved
                } else {
                    assert(j == old_i as int);
                    lemma_bitand_le_right_u8(x1[old_i], x2[old_i]);
                    assert(v <= x2[old_i]);
                    assert((v as int) <= (x2[old_i] as int));
                }
            };

            assert forall|j: int| 0 <= j < i as int ==> (x1[j] == x2[j] ==> out[j] == x1[j]) by {
                assert(0 <= j && j < i as int);
                if j < old_i as int {
                    // preserved
                } else {
                    assert(j == old_i as int);
                    lemma_bitand_eq_self_when_equal_u8(x1[old_i], x2[old_i]);
                    if x1[old_i] == x2[old_i] {
                        assert(out[j] == v);
                        assert(v == (x1[old_i] & x2[old_i]));
                        assert((x1[old_i] & x2[old_i]) == x1[old_i]);
                    }
                }
            };
        }
    }
    out
}
// </vc-code>

}
fn main() {}