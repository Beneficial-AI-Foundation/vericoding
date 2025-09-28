// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

spec fn is_suffix_of<T>(suffix: Seq<T>, full: Seq<T>) -> bool {
    suffix.len() <= full.len() && 
    full.subrange(full.len() - suffix.len(), full.len() as int) == suffix
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rjust(orig: Vec<char>, width: u8, fillchar: char) -> (res: Vec<char>)
    ensures
        res.len() == max_nat(orig.len() as nat, width as nat),
        (orig.len() >= width as usize ==> res@ == orig@) &&
        (orig.len() < width as usize ==> res.len() == width as usize && is_suffix_of(orig@, res@)) &&
        (orig.len() >= width as usize ==> res.len() == orig.len()) &&
        (orig.len() < width as usize ==> res.len() == width as usize) &&
        (orig.len() == 0 ==> res.len() == width as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added proof assertions to verify suffix property */
    if orig.len() >= width as usize {
        orig
    } else {
        let padding_len = width as usize - orig.len();
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < padding_len
            invariant
                i <= padding_len,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == fillchar,
            decreases padding_len - i
        {
            result.push(fillchar);
            i = i + 1;
        }
        let mut j: usize = 0;
        while j < orig.len()
            invariant
                j <= orig.len(),
                result.len() == padding_len + j,
                forall|k: int| 0 <= k < padding_len ==> result@[k] == fillchar,
                forall|k: int| padding_len <= k < padding_len + j ==> result@[k] == orig@[k - padding_len],
            decreases orig.len() - j
        {
            result.push(orig[j]);
            j = j + 1;
        }
        
        proof {
            assert(result.len() == padding_len + orig.len());
            assert(result.len() == width as usize);
            assert(forall|k: int| padding_len <= k < result.len() ==> result@[k] == orig@[k - padding_len]);
            
            // Prove that orig is a suffix of result
            let start_idx = (result.len() - orig.len()) as int;
            assert(start_idx == padding_len as int);
            assert(result@.subrange(start_idx, result.len() as int).len() == orig@.len());
            assert(forall|k: int| 0 <= k < orig.len() ==> 
                result@.subrange(start_idx, result.len() as int)[k] == orig@[k]);
            assert(result@.subrange(start_idx, result.len() as int) == orig@);
            assert(is_suffix_of(orig@, result@));
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}