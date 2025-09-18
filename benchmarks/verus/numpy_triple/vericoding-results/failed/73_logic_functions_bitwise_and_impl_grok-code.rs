// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub proof fn lemma_and_commutative(a: u32, b: u32)
    ensures
       a & b == b & a
{}

pub proof fn lemma_and_zero(a: u32)
    ensures
       a & 0 == 0
{}

pub proof fn lemma_and_self(a: u32)
    ensures
       a & a == a
{}

pub proof fn lemma_and_le(a: u32, b: u32)
    ensures
        a & b <= a && a & b <= b
{}
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax for forall quantifier in loop invariant with proper #[trigger] and spec indexing using @ */
    let mut result = Vec::new();
    for i in 0..x1.len()
        invariant
            result.len() == i,
            forall|j: int| #[trigger(result@[j])] 0 <= j < i ==> result@[j] == (x1@[j] & x2@[j])
    {
        let val = x1[i] & x2[i];
        result.push(val);
    }
    proof {
        let len_h = x1.len() as int;
        assert forall|i: int| 0 <= i < len_h implies 
            result@[i] == x1@[i] & x2@[i] &&
            x1@[i] & x2@[i] == x2@[i] & x1@[i] &&
            x1@[i] & 0 == 0 &&
            x1@[i] & x1@[i] == x1@[i] &&
            result@[i] <= x1@[i] && result@[i] <= x2@[i]
        by {
            lemma_and_commutative(x1@[i], x2@[i]);
            lemma_and_zero(x1@[i]);
            lemma_and_self(x1@[i]);
            lemma_and_le(x1@[i], x2@[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}