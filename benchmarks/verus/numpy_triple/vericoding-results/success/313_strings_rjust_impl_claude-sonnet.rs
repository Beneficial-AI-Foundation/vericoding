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
/* helper modified by LLM (iteration 3): fixed lemma syntax by removing 'lemma' keyword */
proof fn lemma_rjust_suffix(orig: Seq<char>, res: Seq<char>, fillchar: char, width: usize)
    requires
        orig.len() < width,
        res.len() == width,
        forall|j: int| 0 <= j < (width - orig.len()) as int ==> res[j] == fillchar,
        forall|j: int| 0 <= j < orig.len() as int ==> res[(width - orig.len()) as int + j] == orig[j],
    ensures
        is_suffix_of(orig, res),
{
    let suffix_start = res.len() - orig.len();
    assert(suffix_start == (width - orig.len()) as int);
    assert(res.subrange(suffix_start, res.len() as int) == orig);
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
    /* code modified by LLM (iteration 3): kept same implementation with corrected helper function */
    if orig.len() >= width as usize {
        orig
    } else {
        let mut res = Vec::new();
        let fill_count = width as usize - orig.len();
        
        for i in 0..fill_count
            invariant
                res.len() == i,
                forall|j: int| 0 <= j < i ==> res@[j] == fillchar,
        {
            res.push(fillchar);
        }
        
        for i in 0..orig.len()
            invariant
                res.len() == fill_count + i,
                forall|j: int| 0 <= j < fill_count ==> res@[j] == fillchar,
                forall|j: int| 0 <= j < i ==> res@[fill_count + j] == orig@[j],
        {
            res.push(orig[i]);
        }
        
        proof {
            lemma_rjust_suffix(orig@, res@, fillchar, width as usize);
        }
        
        res
    }
}
// </vc-code>

}
fn main() {}