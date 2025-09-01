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
proof fn filter_len_proof(s: Seq<char>, predicate: FnSpec(char) -> bool) 
    ensures 
        s.filter(predicate).len() <= s.len(),
{
    // Built-in lemma or axiom about filter length
}

proof fn last_char_proof(s: Seq<char>) 
    requires 
        s.len() > 0,
    ensures 
        s.last() == s[s.len() as int - 1],
{
    // Built-in lemma about last element
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
    let n = s.len();
    while i < n
        invariant
            i <= n,
            count == vowels(s@.subrange(0, i as int)).len(),
    {
        let c = s.as_bytes()[i] as char;
        if is_vowel(c) {
            count += 1;
        }
        i += 1;
    }
    
    proof {
        if n > 0 {
            let last_char = s.as_bytes()[n - 1] as char;
            if last_char == 'y' || last_char == 'Y' {
                count += 1;
            }
        }
    }
    
    count
}
// </vc-code>

fn main() {}
}