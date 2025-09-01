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
    let filtered_s = s.filter(|x: char| !is_vowel_spec(x));
    let filtered_s_push_c = s.push(c).filter(|x: char| !is_vowel_spec(x));
    
    assert forall|i: int| 0 <= i < filtered_s.len() implies 
        #[trigger] filtered_s_push_c[i] == filtered_s[i] by {
            let j = s.filter(|x: char| !is_vowel_spec(x)).map_index_to_orig_seq(i);
            assert(s[j] == filtered_s[i]);
            assert(!is_vowel_spec(s[j]));
            assert(s.push(c)[j] == s[j]);
        }
    
    assert(filtered_s_push_c.len() == filtered_s.len() + 1);
    assert(filtered_s_push_c[filtered_s.len() as int] == c);
}

proof fn filter_push_vowel(s: Seq<char>, c: char)
    requires
        is_vowel_spec(c),
    ensures
        s.push(c).filter(|x: char| !is_vowel_spec(x)) == 
        s.filter(|x: char| !is_vowel_spec(x)),
{
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