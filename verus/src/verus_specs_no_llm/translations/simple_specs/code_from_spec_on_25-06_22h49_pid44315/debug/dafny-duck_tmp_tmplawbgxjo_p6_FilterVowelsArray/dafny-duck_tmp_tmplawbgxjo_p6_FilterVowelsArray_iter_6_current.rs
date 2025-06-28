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
    let prefix = s.subrange(0, i);
    let extended = s.subrange(0, i + 1);
    
    if i == 0 {
        // Base case: extending from empty sequence to single element
        assert(prefix.len() == 0);
        assert(FilterVowels(prefix) == seq![]);
        assert(extended.len() == 1);
        assert(extended[0] == s[0]);
        
        // By definition of FilterVowels on single element
        assert(FilterVowels(extended) == 
            if is_vowel(s[0]) { seq![] } else { seq![s[0]] });
    } else {
        // Recursive case: i > 0
        assert(extended == prefix + seq![s[i]]);
        
        // Use the fact that extended can be written as prefix + seq![s[i]]
        // and apply the definition of FilterVowels
        let extended_without_last = extended.subrange(0, extended.len() - 1);
        assert(extended_without_last == prefix);
        
        // Apply induction hypothesis
        if i > 0 {
            lemma_filter_vowels_extend(s, i - 1);
        }
        
        // The definition of FilterVowels tells us:
        // FilterVowels(extended) = FilterVowels(extended.subrange(1, extended.len()))
        //   with first element handling
        assert(extended[0] == s[0]);
        assert(extended.subrange(1, extended.len() as int) == 
               prefix.subrange(1, prefix.len() as int) + seq![s[i]]);
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
    } else {
        lemma_filter_vowels_build(s, i - 1);
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
        if !is_vowel_exec(xs[i]) {
            result.push(xs[i]);
            
            proof {
                lemma_filter_vowels_build(xs@, (i + 1) as int);
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)) + seq![xs[i]@]);
            }
        } else {
            proof {
                lemma_filter_vowels_build(xs@, (i + 1) as int);
                assert(FilterVowels(xs@.subrange(0, (i + 1) as int)) == 
                       FilterVowels(xs@.subrange(0, i as int)));
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(xs@.subrange(0, i as int) == xs@);
    }
    result
}

}