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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}