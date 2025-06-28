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
    decreases i
{
    if i == 0 {
        // Base case
        let prefix = s.subrange(0, 0);
        let single = s.subrange(0, 1);
        assert(prefix.len() == 0);
        assert(single.len() == 1);
        assert(single[0] == s[0]);
        assert(FilterVowels(prefix) == seq![]);
    } else {
        // Inductive case
        let prefix = s.subrange(0, i);
        let extended = s.subrange(0, i + 1);
        
        // The key insight: extended is like s but truncated at i+1
        // So FilterVowels(extended) processes elements 0..i in order
        
        // We can reason about this by the structure of the recursive definition
        assert(extended[0] == s[0]);
        assert(extended.subrange(1, extended.len() as int) == s.subrange(1, i + 1));
        
        // Apply induction on the tail
        if i > 0 {
            lemma_filter_vowels_extend(s.subrange(1, s.len() as int), i - 1);
        }
    }
}

proof fn lemma_filter_vowels_build(s: Seq<char>, i: int)
    requires 0 <= i <= s.len()
    ensures FilterVowels(s.subrange(0, i)) == 
        if i == 0 { seq![] }
        else if is_vowel(s[i-1]) { FilterVowels(s.subrange(0, i-1)) }
        else { FilterVowels(s.subrange(0, i-1)) + seq![s[i-1]] }
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(FilterVowels(s.subrange(0, 0)) == seq![]);
    } else {
        lemma_filter_vowels_extend(s, i - 1);
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
        let old_result = result@;
        let old_i = i;
        
        if !is_vowel_exec(xs[i]) {
            result.push(xs[i]);
            
            proof {
                lemma_filter_vowels_build(xs@, (i + 1) as int);
                assert(xs@[i as int] == xs[i]@);
                assert(!is_vowel(xs@[i as int]));
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)) + seq![xs@[i as int]]);
                assert(result@ == old_result + seq![xs[i]@]);
                assert(result@ == FilterVowels(xs@.subrange(0, i as int)) + seq![xs[i]@]);
            }
        } else {
            proof {
                lemma_filter_vowels_build(xs@, (i + 1) as int);
                assert(xs@[i as int] == xs[i]@);
                assert(is_vowel(xs@[i as int]));
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)));
                assert(result@ == old_result);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(i == xs.len());
        assert(xs@.subrange(0, i as int) == xs@);
        assert(result@ == FilterVowels(xs@));
    }
    result
}

}