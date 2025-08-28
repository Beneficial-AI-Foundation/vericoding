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
exec fn is_vowel_exec(c: char) -> (ret: bool)
    ensures ret == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

proof fn vowels_filter_len_bound(s: Seq<char>)
    ensures vowels(s).len() <= s.len()
{
    assert(vowels(s).len() <= s.len()) by {
        let filtered = s.filter(|c| is_vowel(c));
        assert(filtered.len() <= s.len());
    }
}

proof fn vowels_count_bound(s: &str)
    requires s@.len() <= u32::MAX
    ensures vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) { 1int } else { 0int } <= u32::MAX
{
    vowels_filter_len_bound(s@);
    assert(vowels(s@).len() <= s@.len());
    assert(vowels(s@).len() <= u32::MAX);
    if s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y') {
        assert(vowels(s@).len() + 1 <= s@.len() + 1);
        assert(s@.len() + 1 <= u32::MAX + 1);
    }
}

spec fn len_spec(s: &str) -> usize
{
    s@.len() as usize
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
    let mut count = 0u32;
    let mut i = 0usize;
    let len = s@.len() as usize;
    
    proof { vowels_count_bound(s); }
    
    while i < len
        invariant
            len == s@.len() as usize,
            i <= len,
            count == vowels(s@.subrange(0, i as int)).len(),
            count <= u32::MAX - 1,
    {
        let c = s.get_char(i);
        if is_vowel_exec(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    if s@.len() > 0 {
        let last_char = s.get_char(s@.len() as usize - 1);
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    proof {
        assert(s@.subrange(0, s@.len()) =~= s@);
        assert(count == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) { 1int } else { 0int });
    }
    
    count
}
// </vc-code>

}
fn main() {}