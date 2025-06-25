use vstd::prelude::*;

verus! {

const VOWELS: Set<char> = set!['a', 'e', 'i', 'o', 'u'];

spec fn filter_vowels(xs: Seq<char>) -> Seq<char>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else if VOWELS.contains(xs[xs.len() - 1]) {
        filter_vowels(xs.subrange(0, xs.len() - 1)).push(xs[xs.len() - 1])
    } else {
        filter_vowels(xs.subrange(0, xs.len() - 1))
    }
}

pub fn filter_vowels_array(xs: &[char]) -> (ys: Vec<char>)
    ensures(filter_vowels(xs@) == ys@)
{
}

}