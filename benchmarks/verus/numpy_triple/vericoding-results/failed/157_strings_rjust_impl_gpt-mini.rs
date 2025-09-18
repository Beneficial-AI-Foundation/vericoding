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
/* helper modified by LLM (iteration 4): expose vector as sequence */
spec fn seq_of_vec_char(v: Vec<char>) -> Seq<char> { v@ }
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
    /* code modified by LLM (iteration 4): build padded vector using int counters and invariants */
    let orig_len: int = orig.len() as int;
    if orig_len >= width as int {
        orig
    } else {
        let pad: int = width as int - orig_len;
        let mut res: Vec<char> = Vec::new();
        let mut i: int = 0;
        while i < pad {
            invariant 0 <= i && i <= pad;
            invariant res.len() as int == i;
            invariant forall |k: int| 0 <= k && k < i ==> res@[k] == fillchar;
            res.push(fillchar);
            i = i + 1;
        }
        let mut j: int = 0;
        while j < orig_len {
            invariant 0 <= j && j <= orig_len;
            invariant res.len() as int == pad + j;
            invariant forall |k: int| 0 <= k && k < pad ==> res@[k] == fillchar;
            invariant forall |k: int| 0 <= k && k < j ==> res@[(pad + k) as int] == orig@[k];
            res.push(orig@[j]);
            j = j + 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}