// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() as int - 1)) + 
    (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed this empty helper section to clean up the code. */
// </vc-helpers>

// <vc-spec>
fn normalize_bit_string(s: Vec<char>) -> (t: Vec<char>)
  ensures 
    valid_bit_string(t@) &&
    t@.len() > 0 &&
    (t@.len() > 1 ==> t@[0] != '0') &&
    (valid_bit_string(s@) ==> str2int(s@) == str2int(t@))
// </vc-spec>
// <vc-code>
{
    let mut result_vec: Vec<char> = Vec::new();
    let s_len = s.len();

    if s_len == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut first_one_idx: Option<usize> = None;
    for i in 0..s_len {
        if s[i] == '1' {
            first_one_idx = Some(i);
            break;
        }
    }

    match first_one_idx {
        Some(idx) => {
            for i in idx..s_len {
                result_vec.push(s[i]);
            }
            proof {
                if valid_bit_string(s@) {
                    let s_prime = s@;
                    let trimmed_s_prime = s_prime.subrange(idx as int, s_prime.len() as int);
                    assert(str2int(s_prime) == str2int(trimmed_s_prime));
                    assert(result_vec@ == trimmed_s_prime);
                }
            }
        }
        None => {
            // All zeros or empty string
            result_vec.push('0');
            proof {
                if valid_bit_string(s@) {
                    assert(str2int(s@) == 0);
                    assert(result_vec@ == seq!['0']);
                }
            }
        }
    }

    result_vec
}
// </vc-code>


}

fn main() {}