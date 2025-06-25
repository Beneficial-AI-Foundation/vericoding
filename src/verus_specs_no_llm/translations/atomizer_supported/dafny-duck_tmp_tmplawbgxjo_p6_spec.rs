// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FilterVowelsArray(xs: Vec<char>) -> (ys: Vec<char>)
    ensures fresh(ys),
            FilterVowels(xs[..]) == ys[..]
{
}

}