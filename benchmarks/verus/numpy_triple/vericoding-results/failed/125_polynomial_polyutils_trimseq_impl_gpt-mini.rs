// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer min */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() &&

                (forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): find last non-zero index and construct result with trailing zeros */
    let n = seq.len();
    if n == 0 {
        seq
    } else if seq[n - 1] != 0.0f32 {
        seq
    } else {
        let mut idx: int = n as int - 1;
        while idx > 0 && seq[idx as usize] == 0.0f32
            invariant 0 <= idx && idx < n as int;
            invariant forall|j: int| idx < j && j < n as int ==> seq[j as usize] == 0.0f32;
            decreases idx + 1;
        {
            idx -= 1;
        }
        let k_int: int = idx;
        let mut result = Vec::<f32>::new();
        let mut i: usize = 0usize;
        while i < n
            invariant i <= n;
            invariant result.len() == i;
            invariant forall|ii: int| 0 <= ii && ii < i as int ==> ((ii <= k_int ==> result[ii as usize] == seq[ii as usize]) && (ii > k_int ==> result[ii as usize] == 0.0f32));
            decreases n - i;
        {
            if (i as int) <= k_int {
                result.push(seq[i]);
            } else {
                result.push(0.0f32);
            }
            i += 1;
        }
        proof {
            assert(0 <= k_int && k_int < n as int);
            assert(forall|j: int| k_int < j && j < n as int ==> seq[j as usize] == 0.0f32);
            assert(forall|i0: int| 0 <= i0 && i0 <= k_int ==> result[i0 as usize] == seq[i0 as usize]);
            assert(forall|i0: int| k_int < i0 && i0 < result.len() as int ==> result[i0 as usize] == 0.0f32);
            if k_int > 0 {
                assert(seq[k_int as usize] != 0.0f32);
            }
        }
        result
    }
}
// </vc-code>

}
fn main() {}