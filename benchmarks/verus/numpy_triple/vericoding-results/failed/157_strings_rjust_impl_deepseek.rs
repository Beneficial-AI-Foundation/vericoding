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
/* helper modified by LLM (iteration 5): fixed type conversion issues and added lemma for conversion between nat and usize */
spec fn padding_amount(orig_len: nat, width: nat) -> nat {
    max_nat(width, orig_len) - orig_len
}

proof fn lemma_usize_to_nat(n: usize) -> (m: nat)
    ensures m == n as nat
{
    n as nat
}

proof fn lemma_suffix_verification(orig: Seq<char>, result: Seq<char>, padding: nat)
    requires result.len() == padding + orig.len()
    ensures is_suffix_of(orig, result)
{
    assert(result.subrange(padding as int, result.len() as int) == orig);
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
/* code modified by LLM (iteration 5): fixed nat/int conversion by using ghost variables and proper type handling */
{
    let orig_len = orig.len();
    
    if orig_len >= width as usize {
        orig
    } else {
        ghost {
            let orig_len_nat = orig_len as nat;
            let padding_nat = padding_amount(orig_len_nat, width);
            assert(padding_nat == width - orig_len_nat);
        }
        
        let padding = (width - orig_len as nat) as usize;
        
        let mut result = Vec::new();
        
        let mut i: usize = 0;
        while i < padding
            invariant
                0 <= i <= padding,
                result.len() == i
        {
            result.push(fillchar);
            i += 1;
        }
        
        result.extend(orig);
        
        proof {
            let orig_len_nat = orig_len as nat;
            let padding_nat = padding_amount(orig_len_nat, width);
            lemma_suffix_verification(orig@, result@, padding_nat);
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}