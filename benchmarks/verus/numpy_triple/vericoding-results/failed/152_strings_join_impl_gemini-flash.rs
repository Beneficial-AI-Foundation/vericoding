// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper block as it was empty */
// </vc-helpers>

// <vc-spec>
spec fn join_chars(separator: Seq<char>, chars: Seq<char>) -> Seq<char>
    decreases chars.len()
{
    if chars.len() <= 1 {
        chars
    } else {
        chars.take(1) + separator + join_chars(separator, chars.skip(1))
    }
}

spec fn string_to_chars(s: Seq<char>) -> Seq<char> {
    s
}

spec fn chars_to_string_len(chars: Seq<char>) -> nat {
    chars.len()
}

fn join(sep: Vec<String>, seq: Vec<String>) -> (result: Vec<String>)
    requires sep.len() == seq.len(),
    ensures
        result.len() == sep.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let s = seq[i]@;
            let separator = sep[i]@;

            (s.len() <= 1 ==> result[i]@ == s) &&
            (s.len() > 1 ==> result[i]@ == join_chars(separator, s)) &&

            (s.len() > 1 ==> result[i]@.len() == s.len() + (s.len() - 1) * separator.len()) &&

            (s.len() == 0 ==> result[i]@.len() == 0) &&

            (s.len() == 1 ==> result[i]@ == s) &&

            (s.len() > 0 ==> result[i]@.len() > 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `char_seq.len() as nat` to `char_seq.len()` where appropriate to avoid `nat` in ghost code. */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;

    while i < seq.len()
        invariant
            0 <= i && i <= seq.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let s = seq[j as usize]@;
                let separator = sep[j as usize]@;
                (s.len() <= 1 ==> result[j as usize]@ == s) &&
                (s.len() > 1 ==> result[j as usize]@ == join_chars(separator, s)) &&
                (s.len() > 1 ==> result[j as usize]@.len() == s.len() + (s.len() - 1) * separator.len()) &&
                (s.len() == 0 ==> result[j as usize]@.len() == 0) &&
                (s.len() == 1 ==> result[j as usize]@ == s) &&
                (s.len() > 0 ==> result[j as usize]@.len() > 0)
            }
    {
        let s = &seq[i];
        let separator = &sep[i];
        let char_seq = s@;
        let sep_char_seq = separator@;

        let joined_char_seq = if char_seq.len() <= 1 { /* Changed type here */
            char_seq
        } else {
            join_chars(sep_char_seq, char_seq)
        };

        proof {
            if char_seq.len() <= 1 { /* Changed type here */
                assert(joined_char_seq == char_seq);
            } else {
                assert(joined_char_seq == join_chars(sep_char_seq, char_seq));
            }

            if char_seq.len() <= 1 { /* Changed type here */
                assert(joined_char_seq.len() == char_seq.len());
            }

            assert( (char_seq.len() <= 1 ==> joined_char_seq == char_seq) ); /* Changed type here */
            assert( (char_seq.len() > 1 ==> joined_char_seq == join_chars(sep_char_seq, char_seq)) ); /* Changed type here */

            if char_seq.len() > 1 { /* Changed type here */
                assert(joined_char_seq.len() == char_seq.len() + (char_seq.len() - 1) * sep_char_seq.len());
            }
            if char_seq.len() == 0 { /* Changed type here */
                assert(joined_char_seq.len() == 0);
            }
            if char_seq.len() == 1 { /* Changed type here */
                assert(joined_char_seq == char_seq);
                assert(joined_char_seq.len() == char_seq.len());
            }
            if char_seq.len() > 0 { /* Changed type here */
                assert(joined_char_seq.len() >= 0);
                assert(0 <= char_seq.len());
                if char_seq.len() == 1 { /* Changed type here */
                    assert(joined_char_seq.len() == char_seq.len());
                } else if char_seq.len() > 1 { /* Changed type here */
                    assert(joined_char_seq.len() > 0); 
                } else if char_seq.len() == 0 { /* Changed type here */
                    assert(joined_char_seq.len() == 0);
                }
            }
        }

        let u8_vec: Vec<u8> = joined_char_seq.into_iter().map(|c| c as u8).collect();
        result.push(String::from_utf8(u8_vec).unwrap());
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}