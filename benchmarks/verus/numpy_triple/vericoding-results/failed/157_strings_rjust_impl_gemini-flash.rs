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
/* helper modified by LLM (iteration 5): removed as it's not being used and the logic can be handled directly */
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
/* code modified by LLM (iteration 5): Fixed type errors by keeping all length calculations in `usize` or `nat` based on context. `num_fill_chars` is correctly typed as `nat`. */
{
    let orig_len_usize: usize = orig.len();
    let width_usize: usize = width as usize;

    if orig_len_usize >= width_usize {
        orig
    } else {
        let num_fill_chars: nat = (width_usize - orig_len_usize) as nat;
        let mut res: Vec<char> = Vec::new();

        let mut i: usize = 0;
        while i < num_fill_chars as usize
            invariant
                0 <= i && i <= num_fill_chars as usize,
                res.len() == i,
        {
            res.push(fillchar);
            i = i + 1;
        }

        let mut j: usize = 0;
        while j < orig_len_usize
            invariant
                0 <= j && j <= orig_len_usize,
                res.len() == num_fill_chars as usize + j,
        {
            let c = *orig.get(j).expect("index out of bounds");
            res.push(c);
            j = j + 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}