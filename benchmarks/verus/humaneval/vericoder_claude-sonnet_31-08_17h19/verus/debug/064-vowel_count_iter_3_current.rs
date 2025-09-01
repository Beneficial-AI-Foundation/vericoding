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
proof fn lemma_filter_len_bound<T>(s: Seq<T>, f: spec_fn(T) -> bool)
    ensures s.filter(f).len() <= s.len()
{
    if s.len() == 0 {
    } else {
        lemma_filter_len_bound(s.drop_last(), f);
    }
}

proof fn lemma_vowels_len_bound(s: Seq<char>)
    ensures vowels(s).len() <= s.len()
{
    lemma_filter_len_bound(s, |c| is_vowel(c));
}

fn is_vowel_exec(c: char) -> (ret: bool)
    ensures ret == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
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
    let len = s.unicode_len();
    
    proof {
        lemma_vowels_len_bound(s@);
    }
    
    while i < len
        invariant
            i <= len,
            len == s@.len(),
            count == vowels(s@.subrange(0, i as int)).len(),
            s@.len() <= u32::MAX,
    {
        let c = s.get_char(i);
        if is_vowel_exec(c) {
            count = count + 1;
        }
        i = i + 1;
        
        proof {
            assert(s@.subrange(0, i as int) == s@.subrange(0, (i - 1) as int).push(c));
        }
    }
    
    assert(i == len);
    assert(s@.subrange(0, i as int) == s@);
    
    if len > 0 {
        let last_char = s.get_char(len - 1);
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
        
        assert(s@.last() == last_char);
    }
    
    count
}
// </vc-code>

fn main() {}
}