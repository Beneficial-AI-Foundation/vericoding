use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

// <vc-helpers>
proof fn vowels_filter_len_bound(s: Seq<char>)
    ensures vowels(s).len() <= s.len()
{
    /* code modified by LLM (iteration 5): removed invalid import and broadcast, using basic filter property */
    assert(vowels(s) =~= s.filter(|c| is_vowel(c)));
}

proof fn vowels_count_bound(s: &str)
    requires s@.len() <= u32::MAX
    ensures vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) { 1int } else { 0int } <= u32::MAX
{
    vowels_filter_len_bound(s@);
    assert(vowels(s@).len() <= s@.len());
    assert(s@.len() <= u32::MAX);
}

exec fn is_vowel_exec(c: char) -> (ret: bool)
    ensures ret == is_vowel(c)
{
    /* code modified by LLM (iteration 5): exec version of is_vowel for use in implementation */
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def remove_vowels(string: str) -> Nat"
docstring: |
Write a function vowels_count which takes a string representing
a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
vowel, but only when it is at the end of the given word.
test_cases:
- input: "abcde"
expected_output: 2
- input: "ACEDY"
expected_output: 3
*/
// </vc-description>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    proof {
        vowels_count_bound(s);
    }
    
    /* code modified by LLM (iteration 5): use s.len() instead of s.unicode_len() for exec mode */
    while i < s.len()
        invariant
            i <= s.len(),
            count == vowels(s@.subrange(0, i as int)).len(),
            s@.len() <= u32::MAX,
    {
        let c = s.get_char(i);
        /* code modified by LLM (iteration 5): use exec version of is_vowel */
        if is_vowel_exec(c) {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            /* code modified by LLM (iteration 5): fixed subrange relationship proof */
            assert(s@.subrange(0, i as int) == s@.subrange(0, (i - 1) as int).push(c));
            if is_vowel(c) {
                assert(vowels(s@.subrange(0, i as int)) == vowels(s@.subrange(0, (i - 1) as int)).push(c));
            } else {
                assert(vowels(s@.subrange(0, i as int)) == vowels(s@.subrange(0, (i - 1) as int)));
            }
        }
    }
    
    /* code modified by LLM (iteration 5): use s.len() instead of s.unicode_len() for exec mode */
    if s.len() > 0 {
        let last_char = s.get_char(s.len() - 1);
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    proof {
        /* code modified by LLM (iteration 5): use s.len() in proof assertion */
        assert(s@.subrange(0, s.len() as int) == s@);
        assert(count == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) { 1int } else { 0int });
    }
    
    count
}
// </vc-code>

}
fn main() {}