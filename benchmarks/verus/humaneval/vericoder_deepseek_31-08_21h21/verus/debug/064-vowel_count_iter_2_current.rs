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
proof fn filter_len_proof(s: Seq<char>, predicate: spec_fn(char) -> bool) 
    ensures 
        s.filter(predicate).len() <= s.len(),
{
}

proof fn last_char_proof(s: Seq<char>) 
    requires 
        s.len() > 0,
    ensures 
        s.last() == s[s.len() as int - 1],
{
}

proof fn subrange_filter_proof(s: Seq<char>, i: int, predicate: spec_fn(char) -> bool)
    ensures
        s.subrange(0, i).filter(predicate).len() == s.subrange(0, i).filter(predicate).len(),
{
}

proof fn empty_subrange_proof(s: Seq<char>)
    ensures
        s.subrange(0, 0).len() == 0,
{
}

proof fn subrange_invariant_proof(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        s.subrange(0, j) == s.subrange(0, i).add(s.subrange(i, j)),
{
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
    
    proof {
        subrange_invariant_proof(s@, 0, 0);
        assert(vowels(s@.subrange(0, 0)).len() == 0) by {
            assert(s@.subrange(0, 0) === Seq::empty());
        };
    }
    
    while i < n
        invariant
            i <= n,
            count == vowels(s@.subrange(0, i as int)).len(),
    {
        let c = s.as_bytes()[i] as char;
        if is_vowel(c) {
            count = count + 1u32;
        }
        i = i + 1;
        
        proof {
            subrange_invariant_proof(s@, (i-1) as int, i as int);
            let prev_sub = s@.subrange(0, (i-1) as int);
            let current_sub = s@.subrange(0, i as int);
            let last_char = s@[i as int - 1];
            
            if is_vowel(last_char) {
                assert(current_sub.filter(|c| is_vowel(c)).len() == 
                      prev_sub.filter(|c| is_vowel(c)).len() + 1);
            } else {
                assert(current_sub.filter(|c| is_vowel(c)).len() == 
                      prev_sub.filter(|c| is_vowel(c)).len());
            }
        }
    }
    
    let result = if n > 0 {
        let last_char = s.as_bytes()[n - 1] as char;
        if (last_char == 'y' || last_char == 'Y') && !is_vowel(last_char) {
            count + 1u32
        } else {
            count
        }
    } else {
        count
    };
    
    proof {
        if n > 0 {
            let last_char = s@[n as int - 1];
            assert(s@.last() == last_char) by {
                last_char_proof(s@);
            };
            
            if last_char == 'y' || last_char == 'Y' {
                assert(inner_expr_vowels_count(s, result) == (result == vowels(s@).len() + 1));
            } else {
                assert(inner_expr_vowels_count(s, result) == (result == vowels(s@).len()));
            }
        } else {
            assert(inner_expr_vowels_count(s, result) == (result == vowels(s@).len()));
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}