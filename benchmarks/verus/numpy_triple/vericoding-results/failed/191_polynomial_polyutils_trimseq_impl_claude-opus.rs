// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() as int &&

                (forall|j: int| k < j < seq.len() as int ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() as int ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error in invariant by adding parentheses */
    let mut result = Vec::new();
    let n = seq.len();
    
    if n == 0 {
        return result;
    }
    
    let ghost last_nonzero_spec: int = n as int;
    let mut last_nonzero: usize = n;
    let mut i: usize = n;
    
    while i > 0
        invariant
            i <= n,
            last_nonzero <= n,
            i <= last_nonzero,
            last_nonzero as int == last_nonzero_spec,
            forall|j: int| i as int <= j && j < last_nonzero as int ==> seq[j] == 0.0f32,
            last_nonzero < n ==> seq[last_nonzero] != 0.0f32,
        decreases i
    {
        i = i - 1;
        if seq[i] != 0.0f32 {
            last_nonzero = i;
            proof {
                assert(seq[i] != 0.0f32);
            }
        }
    }
    
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            result.len() == j,
            last_nonzero <= n,
            forall|k: int| (last_nonzero as int < k) && (k < n as int) ==> seq[k] == 0.0f32,
            last_nonzero < n ==> seq[last_nonzero] != 0.0f32,
            forall|k: int| (0 <= k && k < j as int && k <= last_nonzero as int) ==> result[k] == seq[k],
            forall|k: int| (0 <= k && k < j as int && k > last_nonzero as int) ==> result[k] == 0.0f32,
        decreases n - j
    {
        if j <= last_nonzero {
            result.push(seq[j]);
        } else {
            result.push(0.0f32);
        }
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}