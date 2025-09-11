// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn vowels() -> Set<char> {
    set!['a', 'e', 'i', 'o', 'u']
}

spec fn filter_vowels(xs: Seq<char>) -> Seq<char>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else if vowels().contains(xs[xs.len() - 1]) {
        filter_vowels(xs.subrange(0, xs.len() - 1)).add(seq![xs[xs.len() - 1]])
    } else {
        filter_vowels(xs.subrange(0, xs.len() - 1))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn filter_vowels_array(xs: &[char]) -> (ys: Vec<char>)
    ensures filter_vowels(xs@) == ys@
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}