// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn FilterVowelsArray(xs: Vec<char>) -> (ys: Vec<char>)
    ensures
        fresh(ys),
        FilterVowels(xs.spec_index(..)) == ys.spec_index(..)
{
    return Vec::new();
}

}