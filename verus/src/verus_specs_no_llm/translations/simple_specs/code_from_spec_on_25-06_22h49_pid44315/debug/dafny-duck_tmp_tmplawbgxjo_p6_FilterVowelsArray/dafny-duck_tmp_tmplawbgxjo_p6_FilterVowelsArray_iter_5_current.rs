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

proof fn lemma_filter_vowels_extend(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures FilterVowels(s.subrange(0, i + 1)) == 
        if is_vowel(s[i]) {
            FilterVowels(s.subrange(0, i))
        } else {
            FilterVowels(s.subrange(0, i)) + seq![s[i]]
        }
    decreases s.len() - i
{
    let prefix = s.subrange(0, i);
    let extended = s.subrange(0, i + 1);
    
    if i == 0 {
        // Base case: extending from empty sequence
        assert(prefix.len() == 0);
        assert(FilterVowels(prefix) == seq![]);
        assert(extended == seq![s[0]]);
        assert(extended.len() == 1);
        assert(extended[0] == s[0]);
        
        // By definition of FilterVowels on single element
        if is_vowel(s[0]) {
            assert(FilterVowels(extended) == seq![]);
        } else {
            assert(FilterVowels(extended) == seq![s[0]]);
        }
    } else {
        // Recursive case
        assert(prefix.len() > 0);
        assert(extended.len() > 0);
        assert(prefix[0] == s[0]);
        assert(extended[0] == s[0]);
        
        // Apply the recursive definition
        let prefix_rest = FilterVowels(prefix.subrange(1, prefix.len() as int));
        let extended_rest = FilterVowels(extended.subrange(1, extended.len() as int));
        
        // Note that extended.subrange(1, extended.len()) == prefix.subrange(1, prefix.len()) + seq![s[i]]
        assert(extended.subrange(1, extended.len() as int) == 
               prefix.subrange(1, prefix.len() as int) + seq![s[i]]);
        
        // Apply the lemma recursively
        lemma_filter_vowels_extend(s, i - 1);
        
        if is_vowel(s[0]) {
            assert(FilterVowels(prefix) == prefix_rest);
            assert(FilterVowels(extended) == extended_rest);
        } else {
            assert(FilterVowels(prefix) == seq![s[0]] + prefix_rest);
            assert(FilterVowels(extended) == seq![s[0]] + extended_rest);
        }
    }
}

fn FilterVowelsArray(xs: Vec<char>) -> (ys: Vec<char>)
    ensures FilterVowels(xs@) == ys@
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < xs.len()
        invariant
            i <= xs.len(),
            result@ == FilterVowels(xs@.subrange(0, i as int))
    {
        if !is_vowel_exec(xs[i]) {
            result.push(xs[i]);
            
            proof {
                lemma_filter_vowels_extend(xs@, i as int);
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)) + seq![xs[i]@]);
                assert(result@ == FilterVowels(xs@.subrange(0, i as int)) + seq![xs[i]@]);
            }
        } else {
            proof {
                lemma_filter_vowels_extend(xs@, i as int);
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)));
            }
        }
        
        i += 1;
    }
    
    assert(i == xs.len());
    assert(xs@.subrange(0, i as int) == xs@);
    result
}

}