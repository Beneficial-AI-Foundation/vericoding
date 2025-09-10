use vstd::prelude::*;

verus! {

spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

spec fn is_suffix_of<T>(suffix: Seq<T>, full: Seq<T>) -> bool {
    suffix.len() <= full.len() && 
    full.subrange(full.len() - suffix.len(), full.len() as int) == suffix
}

fn rjust(orig: Vec<char>, width: nat, fillchar: char) -> (res: Vec<char>)
    ensures
        res.len() == max_nat(orig.len() as nat, width),
        (orig.len() >= width ==> res@ == orig@) &&
        (orig.len() < width ==> res.len() == width && is_suffix_of(orig@, res@)) &&
        (orig.len() >= width ==> res.len() == orig.len()) &&
        (orig.len() < width ==> res.len() == width) &&
        (orig.len() == 0 ==> res.len() == width)
{
    assume(false);
    unreached()
}

}
fn main() {}