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
    // The filter operation on sequences preserves the length bound
    // This should be provable automatically by Verus
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
    
    while i < s@.len() as usize
        invariant 
            i <= s@.len(),
            count == vowels(s@.subrange(0, i as int)).len(),
            count <= i,
    {
        if is_vowel(s.get_char(i)) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    if s@.len() > 0nat && (s.get_char((s@.len() - 1nat) as usize) == 'y' || s.get_char((s@.len() - 1nat) as usize) == 'Y') {
        count = count + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) == s@);
        assert(count == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) { 1int } else { 0int });
    }
    
    count
}
// </vc-code>

}
fn main() {}