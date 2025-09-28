// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): replaced wrapping arithmetic with standard operations */
    let len1_usize = c1.len();
    let len2_usize = c2.len();
    let result_len_usize = if len1_usize < len2_usize { len1_usize } else { len2_usize };
    let max_len_usize = if len1_usize > len2_usize { len1_usize } else { len2_usize };
    
    let mut result = Vec::with_capacity(max_len_usize);
    
    let mut i: usize = 0;
    while i < result_len_usize
        invariant
            0 <= i as int <= result_len_usize as int,
            result.len() == i,
            i <= c1.len(),
            i <= c2.len(),
            forall|j: int| 0 <= j < i as int ==> result@[j] == c1@[j] - c2@[j],
        decreases (result_len_usize as int - i as int)
    {
        proof {
            assert(i < c1.len());
            assert(i < c2.len());
        }
        result.push(c1[i] - c2[i]);
        i += 1;
    }
    
    if len1_usize > len2_usize {
        let mut i: usize = result_len_usize;
        while i < len1_usize
            invariant
                result_len_usize as int <= i as int <= len1_usize as int,
                result.len() == i,
                forall|j: int| 0 <= j < result_len_usize as int ==> result@[j] == c1@[j] - c2@[j],
                forall|j: int| result_len_usize as int <= j < i as int ==> result@[j] == c1@[j],
            decreases (len1_usize as int - i as int)
        {
            proof {
                assert(i < c1.len());
            }
            result.push(c1[i]);
            i += 1;
        }
    } else if len2_usize > len1_usize {
        let mut i: usize = result_len_usize;
        while i < len2_usize
            invariant
                result_len_usize as int <= i as int <= len2_usize as int,
                result.len() == i,
                forall|j: int| 0 <= j < result_len_usize as int ==> result@[j] == c1@[j] - c2@[j],
                forall|j: int| result_len_usize as int <= j < i as int ==> result@[j] == -c2@[j],
            decreases (len2_usize as int - i as int)
        {
            proof {
                assert(i < c2.len());
            }
            result.push(-c2[i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}