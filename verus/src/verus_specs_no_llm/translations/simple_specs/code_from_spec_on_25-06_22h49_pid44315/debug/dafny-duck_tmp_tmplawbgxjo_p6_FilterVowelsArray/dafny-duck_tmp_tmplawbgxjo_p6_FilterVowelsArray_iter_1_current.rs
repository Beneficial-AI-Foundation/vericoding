use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn FilterVowels(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let rest = FilterVowels(s.subrange(1, s.len() as int));
        if is_vowel(s[0]) {
            rest
        } else {
            seq![s[0]] + rest
        }
    }
}

fn is_vowel_exec(c: char) -> (result: bool)
    ensures result == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

fn FilterVowelsArray(xs: Vec<char>) -> (ys: Vec<char>)
    ensures
        fresh(ys),
        FilterVowels(xs.spec_index(..)) == ys.spec_index(..)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < xs.len()
        invariant
            i <= xs.len(),
            result.spec_index(..) == FilterVowels(xs.spec_index(..i as int))
    {
        if !is_vowel_exec(xs[i]) {
            result.push(xs[i]);
        }
        i += 1;
    }
    
    assert(xs.spec_index(..i as int) == xs.spec_index(..));
    result
}

}