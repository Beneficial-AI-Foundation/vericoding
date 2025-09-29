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
/* helper modified by LLM (iteration 2): Proves that the right operand is a suffix of the concatenation */
proof fn suffix_of_concat_right<A>(a: Seq<A>, b: Seq<A>)
    ensures
        is_suffix_of(b, a + b),
{
    assert((a + b).len() == a.len() + b.len());
    assert(b.len() <= (a + b).len());
    assert(((a + b).len() - b.len()) as int == a.len() as int);
    assert((a + b).subrange(a.len() as int, (a + b).len() as int) == b);
}
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
    /* code modified by LLM (iteration 2): Implement rjust with padding then append, using ghost variables for views to avoid exec/spec mixing */
    let mut orig = orig;
    if orig.len() >= width as usize {
        return orig;
    } else {
        let orig_len: usize = orig.len();
        let pad_len_usize: usize = (width as usize) - orig_len;

        let mut res: Vec<char> = Vec::new();

        let mut i: usize = 0;
        while i < pad_len_usize
            invariant
                i <= pad_len_usize,
                res.len() == i,
                forall|k: int| 0 <= k && k < i as int ==> res@[k] == fillchar,
            decreases pad_len_usize - i
        {
            res.push(fillchar);
            i = i + 1;
        }

        let ghost prefix: Seq<char> = res@;
        let ghost orig_seq: Seq<char> = orig@;

        res.append(&mut orig);

        proof {
            assert(res@ == prefix + orig_seq);
            suffix_of_concat_right::<char>(prefix, orig_seq);
            assert(is_suffix_of(orig_seq, res@));
        }

        assert(res.len() == pad_len_usize + orig_len);
        assert(res.len() == width as usize);

        res
    }
}
// </vc-code>

}
fn main() {}