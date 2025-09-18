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
fn rjust(orig: Vec<char>, width: nat, fillchar: char) -> (res: Vec<char>)
    ensures
        res.len() == max_nat(orig.len() as nat, width),
        (orig.len() >= width ==> res@ == orig@) &&
        (orig.len() < width ==> res.len() == width && is_suffix_of(orig@, res@)) &&
        (orig.len() >= width ==> res.len() == orig.len()) &&
        (orig.len() < width ==> res.len() == width) &&
        (orig.len() == 0 ==> res.len() == width)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatches by casting width to usize */
    let orig_len = orig.len();
    if orig_len >= width as usize {
        orig
    } else {
        let padding_len: usize = (width as usize) - orig_len;
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < padding_len
            invariant
                i <= padding_len,
                result.len() == i,
                forall|j: int| 0 <= j < i as int ==> result@[j] == fillchar
        {
            result.push(fillchar);
            i = i + 1;
        }
        let mut j: usize = 0;
        while j < orig_len
            invariant
                j <= orig_len,
                result.len() == padding_len + j,
                forall|k: int| 0 <= k < padding_len as int ==> result@[k] == fillchar,
                forall|k: int| 0 <= k < j as int ==> result@[(padding_len as int) + k] == orig@[k]
        {
            result.push(orig[j]);
            j = j + 1;
        }
        assert(result.len() == width as usize);
        assert(is_suffix_of(orig@, result@));
        result
    }
}
// </vc-code>

}
fn main() {}