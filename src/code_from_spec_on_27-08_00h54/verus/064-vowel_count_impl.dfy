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
    // The filter operation on sequences preserves length bounds
}

proof fn vowels_count_bound(s: Seq<char>)
    requires s.len() <= u32::MAX
    ensures vowels(s).len() + 1 <= u32::MAX
{
    vowels_filter_len_bound(s);
    assert(vowels(s).len() <= s.len() <= u32::MAX);
}

spec fn str_len(s: &str) -> usize;

spec fn str_nth_char(s: &str, i: usize) -> char
    recommends i < str_len(s);

spec fn str_last_char(s: &str) -> char
    recommends str_len(s) > 0;
// </vc-helpers>

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
    let s_len = s@.len();
    
    proof {
        vowels_count_bound(s@);
    }
    
    while i < s_len
        invariant
            i <= s_len,
            s_len == s@.len(),
            s@.len() <= u32::MAX,
            count == vowels(s@.subrange(0, i as int)).len(),
            count <= u32::MAX - 1,
    {
        let c = s@[i as int];
        
        if is_vowel(c) {
            count = count + 1;
        }
        
        proof {
            assert(s@.subrange(0, i as int + 1) == s@.subrange(0, i as int).push(s@[i as int]));
            if is_vowel(c) {
                assert(vowels(s@.subrange(0, i as int + 1)) == vowels(s@.subrange(0, i as int)).push(c));
            } else {
                assert(vowels(s@.subrange(0, i as int + 1)) == vowels(s@.subrange(0, i as int)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) == s@);
    }
    
    if s_len > 0 {
        let last_char = s@[s_len - 1];
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}