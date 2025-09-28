// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower_char(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn char_set_from_string(s: Seq<char>) -> Set<char> {
    Set::new(|c: char| exists|i: int| 0 <= i < s.len() && #[trigger] to_lower_char(s[i]) == c)
}
// </vc-preamble>

// <vc-helpers>
fn contains_char(v: &Vec<char>, target: char) -> (b: bool)
    ensures b == v@.contains(target),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            !v@.subrange(0, i).contains(target),
        decreases v.len() - i
    {
        if v[i] == target {
            return true;
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, v@.len()) =~= v@);
    }
    return false;
}

#[verifier::spinoff_prover]
proof fn lemma_to_lower_is_idempotent(c: char)
    ensures
        to_lower_char(to_lower_char(c)) == to_lower_char(c),
{}

/* helper modified by LLM (iteration 3): keeping correct helper from previous turn */
proof fn lemma_char_set_from_string_append_char(s: Seq<char>, c: char)
    ensures
        char_set_from_string(s.push(c)) == char_set_from_string(s).insert(to_lower_char(c)),
{
    vstd::set_lib::assert_sets_equal!(
        char_set_from_string(s.push(c)),
        char_set_from_string(s).insert(to_lower_char(c))
    );
}
// </vc-helpers>

// <vc-spec>
fn count_distinct_characters(s: &str) -> (count: usize)
    ensures 
        count <= s@.len(),
        count == char_set_from_string(s@).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using the correct lemma name */
{
    let s_chars: Vec<char> = s.chars().collect();

    let mut distinct_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_chars@ == s@,
            distinct_chars@.len() <= i,
            forall|k: int| 0 <= k < distinct_chars@.len() ==> 
                distinct_chars@[k] == to_lower_char(distinct_chars@[k]),
            forall|j1: int, j2: int| 0 <= j1 < j2 < distinct_chars@.len() ==>
                distinct_chars@[j1] != distinct_chars@[j2],
            distinct_chars@.to_set() == char_set_from_string(s_chars@.subrange(0, i)),
        decreases s_chars.len() - i
    {
        let current_char = s_chars[i];
        let lower_char = to_lower_char(current_char);

        lemma_to_lower_is_idempotent(current_char);

        let has_char = contains_char(&distinct_chars, lower_char);

        proof {
            lemma_char_set_from_string_append_char(s_chars@.subrange(0, i), current_char);
        }

        if !has_char {
            distinct_chars.push(lower_char);
        }
        
        i = i + 1;
    }

    proof {
        vstd::seq_lib::lemma_len_of_set_from_seq_if_distinct(distinct_chars@);
    }
    
    return distinct_chars.len();
}
// </vc-code>


}

fn main() {}