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
/* helper modified by LLM (iteration 5): No changes needed, helper is correct. */
fn create_fill_vec(len: usize, fillchar: char) -> (res: Vec<char>)
    ensures
        res.len() == len,
        res@.len() == len as nat,
        forall|i: int| 0 <= i < len as int ==> res@[i] == fillchar,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            res.len() == i,
            res@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> res@[j] == fillchar,
        decreases len - i,
    {
        res.push(fillchar);
        i = i + 1;
    }
    res
}
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
    /* code modified by LLM (iteration 5): fixed compilation error by using correct lemma path. */
    let orig_len = orig.len();
    if orig_len >= width as usize {
        orig
    } else {
        let padding_len = width as usize - orig_len;
        let mut padding = create_fill_vec(padding_len, fillchar);

        let old_padding_seq = padding@;
        let orig_seq = orig@;

        let mut orig_mut = orig;
        padding.append(&mut orig_mut);

        proof {
            vstd::seq_lib::lemma_subrange_of_add(old_padding_seq, orig_seq);
            assert(is_suffix_of(orig_seq, padding@));
        }

        padding
    }
}
// </vc-code>

}
fn main() {}