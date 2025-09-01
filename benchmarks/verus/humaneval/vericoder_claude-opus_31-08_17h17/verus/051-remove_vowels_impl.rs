use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
fn is_vowel(c: char) -> (result: bool)
    ensures
        result == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

proof fn filter_push_non_vowel(s: Seq<char>, c: char)
    requires
        !is_vowel_spec(c),
    ensures
        s.push(c).filter(|x: char| !is_vowel_spec(x)) == 
        s.filter(|x: char| !is_vowel_spec(x)).push(c),
{
    let s_push_c = s.push(c);
    let filtered_s = s.filter(|x: char| !is_vowel_spec(x));
    let filtered_s_push_c = s_push_c.filter(|x: char| !is_vowel_spec(x));
    
    assert(s_push_c.len() == s.len() + 1);
    assert(forall|i: int| 0 <= i < s.len() ==> s_push_c[i] == s[i]);
    assert(s_push_c[s.len() as int] == c);
    
    // The filter of s.push(c) contains all elements from filter of s, plus c at the end
    assert(filtered_s_push_c.len() == filtered_s.len() + 1);
    assert(forall|i: int| 0 <= i < filtered_s.len() ==> #[trigger] filtered_s_push_c[i] == filtered_s[i]);
    assert(filtered_s_push_c[filtered_s.len() as int] == c);
    
    assert(filtered_s_push_c =~= filtered_s.push(c));
}

proof fn filter_push_vowel(s: Seq<char>, c: char)
    requires
        is_vowel_spec(c),
    ensures
        s.push(c).filter(|x: char| !is_vowel_spec(x)) == 
        s.filter(|x: char| !is_vowel_spec(x)),
{
    let s_push_c = s.push(c);
    let filtered_s = s.filter(|x: char| !is_vowel_spec(x));
    let filtered_s_push_c = s_push_c.filter(|x: char| !is_vowel_spec(x));
    
    assert(s_push_c.len() == s.len() + 1);
    assert(forall|i: int| 0 <= i < s.len() ==> s_push_c[i] == s[i]);
    assert(s_push_c[s.len() as int] == c);
    
    // Since c is a vowel, it won't be in the filtered sequence
    assert(filtered_s_push_c.len() == filtered_s.len());
    assert(forall|i: int| 0 <= i < filtered_s.len() ==> #[trigger] filtered_s_push_c[i] == filtered_s[i]);
    
    assert(filtered_s_push_c =~= filtered_s);
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    // post-conditions-start
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < str.len()
        invariant
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases
            str.len() - i,
    {
        let c = str[i];
        if !is_vowel(c) {
            proof {
                assert(str@.subrange(0, i as int).push(c) == str@.subrange(0, (i + 1) as int));
                filter_push_non_vowel(str@.subrange(0, i as int), c);
            }
            result.push(c);
        } else {
            proof {
                assert(str@.subrange(0, i as int).push(c) == str@.subrange(0, (i + 1) as int));
                filter_push_vowel(str@.subrange(0, i as int), c);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(str@.subrange(0, str.len() as int) == str@);
    }
    
    result
}
// </vc-code>

} // verus!
fn main() {}