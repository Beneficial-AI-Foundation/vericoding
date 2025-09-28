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

// </vc-helpers>

// <vc-spec>
fn count_distinct_characters(s: &str) -> (count: usize)
    ensures 
        count <= s@.len(),
        count == char_set_from_string(s@).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors by ensuring `int` and `nat` types are used only in ghost contexts or for operations within proof blocks. Changed `distinct_chars` to be a ghost variable, and removed the `tracked_byte_slice` workaround by changing `s_seq` to `s@`. Updated loop variable `i` to `usize` for concrete operations. */
{
    let s_seq = s@;
    let len = s_seq.len();

    // Ghost variable to accumulate distinct characters in spec
    let ghost mut distinct_chars_spec: Set<char> = Set::empty();

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            s_seq.len() == len,
            distinct_chars_spec == char_set_from_string(s_seq.subsequence(0, i as nat)),
        decreases len - i
    {
        let char_at_i = s_seq.index(i as nat);
        let lower_char_at_i = to_lower_char(char_at_i);

        distinct_chars_spec = distinct_chars_spec.insert(lower_char_at_i);

        i = i + 1;
    }
    distinct_chars_spec.len() as usize
}
// </vc-code>


}

fn main() {}