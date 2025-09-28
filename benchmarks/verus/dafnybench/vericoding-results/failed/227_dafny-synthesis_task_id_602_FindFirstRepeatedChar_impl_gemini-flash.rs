use vstd::prelude::*;

verus! {

// <vc-helpers>
fn char_to_usize(c: char) -> usize {
    c as usize
}

const ALPHABET_SIZE: usize = 256; // Assuming ASCII characters

// Helper function to convert a slice of u8 to our sequence type for proofs
fn bytes_to_seq(bytes: &[u8]) -> Seq<u8> {
    Seq::new(bytes.len() as nat, |i: nat| bytes[i as usize])
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    let s_len = s.len();
    if s_len < 2 {
        return (false, 'a');
    }

    let mut seen_chars: [bool; ALPHABET_SIZE] = [false; ALPHABET_SIZE];

    let s_bytes = s.as_bytes();
    let s_seq = bytes_to_seq(s_bytes);

    let mut i: usize = 0;
    while i < s_len
        invariant
            0 <= i as int <= s_len as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] seen_chars[char_to_usize(s_seq.index(k as nat) as char)], // Use .index(k)
            forall|k: int, l: int| 0 <= k < l < i as int ==> s_seq.index(k as nat) != s_seq.index(l as nat), // Use .index(k)
    {
        let current_char_byte = s_seq.index(i as nat); // Use .index(i)
        let current_char = current_char_byte as char;
        let char_idx = char_to_usize(current_char);

        if seen_chars[char_idx] {
            assert(exists|j: int| 0 <= j < i as int && s_seq.index(j as nat) == current_char_byte); // Use .index(j)
            proof {
                // Find the first occurrence of current_char
                let mut first_occurrence_idx: int = 0;
                while first_occurrence_idx < i as int
                    invariant 0 <= first_occurrence_idx <= i as int,
                              forall|k: int| 0 <= k < first_occurrence_idx ==> s_seq.index(k as nat) != current_char_byte,
                {
                    if s_seq.index(first_occurrence_idx as nat) == current_char_byte {
                        break;
                    }
                    first_occurrence_idx += 1;
                }
                assert(s_seq.index(first_occurrence_idx as nat) == current_char_byte);
                assert(first_occurrence_idx < i as int);

                assert(0 <= first_occurrence_idx);
                assert(first_occurrence_idx < i as int);
                assert(s_seq.index(first_occurrence_idx as nat) == current_char_byte);
                assert(s_seq.index(i as nat) == current_char_byte);
            }
            return (true, current_char);
        }
        seen_chars[char_idx] = true;
        i += 1;
    }

    assert(forall|idx_i: int, idx_j: int| 0 <= idx_i < idx_j < s_len as int ==> s_seq.index(idx_i as nat) != s_seq.index(idx_j as nat));

    (false, 'a')
}
// </vc-code>

fn main() {}

}