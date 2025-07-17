// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn FilterVowels(xs: Seq<char>) -> Seq<char>
{
    Seq::empty()
}

spec fn spec_FilterVowelsArray(xs: Vec<char>) -> ys: array<char>
    ensures
        fresh(ys),
        FilterVowels(xs.index(..)) == ys.index(..)
;

proof fn lemma_FilterVowelsArray(xs: Vec<char>) -> (ys: Vec<char>)
    ensures
        fresh(ys),
        FilterVowels(xs.index(..)) == ys.index(..)
{
    Vec::new()
}

}