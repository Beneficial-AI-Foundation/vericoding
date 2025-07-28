use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

fn is_vowel(c: char) -> (is_vowel: bool)
    // post-conditions-start
    ensures
        is_vowel == is_vowel_spec(c),
    // post-conditions-end
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    // post-conditions-start
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed loop invariant and added proper verification logic */
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i,
    {
        /* code modified by LLM (iteration 3): removed problematic variable assignment and simplified proof */
        let current_char = str[i];
        
        if !is_vowel(current_char) {
            result.push(current_char);
            /* code modified by LLM (iteration 3): prove filter property for non-vowel case */
            assert(!is_vowel_spec(current_char));
            assert(str@.subrange(0, (i + 1) as int) == str@.subrange(0, i as int).push(current_char));
            assert(str@.subrange(0, (i + 1) as int).filter(|x: char| !is_vowel_spec(x)) == 
                   str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)).push(current_char));
        } else {
            /* code modified by LLM (iteration 3): prove filter property for vowel case */
            assert(is_vowel_spec(current_char));
            assert(str@.subrange(0, (i + 1) as int) == str@.subrange(0, i as int).push(current_char));
            assert(str@.subrange(0, (i + 1) as int).filter(|x: char| !is_vowel_spec(x)) == 
                   str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)));
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): added final assertion to prove postcondition */
    assert(i == str.len());
    assert(str@.subrange(0, i as int) == str@);
    
    result
}

} // verus!
fn main() {}