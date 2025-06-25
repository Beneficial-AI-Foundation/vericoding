use vstd::prelude::*;

verus! {

const vowels: Set<char> = set!['a', 'e', 'i', 'o', 'u'];

spec fn FilterVowels(xs: Seq<char>) -> Seq<char>
{
    if xs.len() == 0 {
        seq![]
    } else if vowels.contains(xs[xs.len() as int - 1]) {
        FilterVowels(xs.subrange(0, xs.len() as int - 1)).add(seq![xs[xs.len() as int - 1]])
    } else {
        FilterVowels(xs.subrange(0, xs.len() as int - 1))
    }
}

pub fn FilterVowelsArray(xs: &[char]) -> (ys: Vec<char>)
    ensures(FilterVowels(xs@) == ys@)
{
}

}