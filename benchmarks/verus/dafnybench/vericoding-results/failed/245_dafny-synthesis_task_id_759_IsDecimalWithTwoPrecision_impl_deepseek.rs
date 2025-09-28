use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn decimal_position_two_digits(s: Seq<char>) -> (pos: int)
    recommends
        exists|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2
    ensures
        0 <= pos < s.len(),
        s[pos] == '.',
        s.len() - pos - 1 == 2
{
    let i = choose|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2;
    i
}

proof fn no_decimal_position_with_two_digits(s: Seq<char>) 
    requires
        !exists|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2
    ensures
        forall|i: int| 0 <= i < s.len() ==> 
            s[i] != '.' || s.len() - i - 1 != 2
{
}

spec fn chars_match_seq_at_index(s: &str, chars: Vec<char>, i: int) -> bool
    recommends 0 <= i < s@.len()
    ensures chars_match_seq_at_index(s, chars, i) == (chars[i as usize] == s@[i])
{
    chars.len() as int == s@.len() && forall|j: int| 0 <= j < s@.len() ==> chars[j as usize] == s@[j]
}

spec fn chars_match_seq(s: &str, chars: Vec<char>) -> bool
    ensures chars_match_seq(s, chars) == (chars.len() as int == s@.len() && forall|j: int| 0 <= j < s@.len() ==> chars[j as usize] == s@[j])
{
    chars.len() as int == s@.len() && forall|j: int| 0 <= j < s@.len() ==> chars[j as usize] == s@[j]
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let mut has_dot = false;
    let mut dot_index: Option<usize> = None;
    let mut i: usize = 0;
    let s_view = s@;
    let chars: Vec<char> = s.chars().collect();
    proof {
        assert(chars.len() == s_view.len()) by {
            assert(s.chars().count() == s_view.len());
        };
        assert(forall|j: int| 0 <= j < s_view.len() ==> chars[j as usize] == s_view[j]);
    }
    
    while i < s.len()
        invariant
            i <= s_view.len(),
            has_dot == exists|j: int| 0 <= j < i && s_view[j] == '.',
            dot_index.is_some() == has_dot,
            dot_index.is_some() ==> {
                let idx: int = dot_index.get_Some_0() as int;
                0 <= idx < i && s_view[idx] == '.'
            },
            chars.len() == s_view.len(),
            forall|j: int| 0 <= j < s_view.len() ==> chars[j as usize] == s_view[j]
    {
        let c = chars[i];
        if c == '.' {
            if has_dot {
                assert(!(s_view[i] == '.' && i as int < s_view.len()));
                return false;
            }
            has_dot = true;
            dot_index = Some(i);
            assert(s_view[i] == '.');
        }
        i = i + 1;
    }
    
    if !has_dot {
        proof {
            assert(!exists|j: int| 0 <= j < s_view.len() && s_view[j] == '.');
        }
        return false;
    }
    
    let dot_pos = dot_index.unwrap();
    let digits_after_dot = s.len() - dot_pos - 1;
    proof {
        assert(dot_pos < s_view.len());
        assert(s_view[dot_pos as int] == '.');
    }
    if digits_after_dot == 2 {
        proof {
            assert(exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2);
        }
        true
    } else {
        proof {
            assert(!(s@.len() - dot_pos as int - 1 == 2));
            assert(forall|i: int| 0 <= i < s@.len() && s@[i] == '.' ==> s@.len() - i - 1 != 2);
        }
        false
    }
}
// </vc-code>

fn main() {
}

}