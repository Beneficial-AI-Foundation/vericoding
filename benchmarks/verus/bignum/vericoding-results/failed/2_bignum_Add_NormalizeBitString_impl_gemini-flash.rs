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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): No helper functions needed for now. */
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): The main changes focused on resolving the remaining 'int' and 'nat' type errors. I replaced direct `int` indexing with explicit `as usize` casts for `Vec` access and `as nat` casts for `Seq` access where appropriate. For `max_len`, I kept it as `usize` to align with `Vec` and `Seq` lengths. Loop bounds and conditions were also adjusted to use `usize` for lengths and iteration count. */
{
    let s1_seq = s1@;
    let s2_seq = s2@;

    let mut s1_norm = s1_seq;
    let mut s2_norm = s2_seq;

    let max_len: usize = s1_norm.len().max(s2_norm.len());

    while s1_norm.len() < max_len
        invariant
            s1_norm.len() <= max_len,
            s2_norm.len() == max_len,
            valid_bit_string(s1_norm),
            valid_bit_string(s2_norm),
        decreases max_len - s1_norm.len()
    {
        s1_norm = Seq::new(1, &['0']).add(s1_norm);
    }
    while s2_norm.len() < max_len
        invariant
            s1_norm.len() == max_len,
            s2_norm.len() <= max_len,
            valid_bit_string(s1_norm),
            valid_bit_string(s2_norm),
        decreases max_len - s2_norm.len()
    {
        s2_norm = Seq::new(1, &['0']).add(s2_norm);
    }

    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;

    while i < max_len || carry == 1
        invariant
            carry == 0 || carry == 1,
            valid_bit_string(result_vec@),
            result_vec.len() == i,
            (max_len as int - i as int).max(0) + (carry as int) >= 0,
        decreases (max_len as int - i as int).max(0) + (carry as int)
    {
        let digit1 = if i < max_len { (s1_norm.index((max_len - 1 - i) as nat) == '1') as u8 } else { 0 };
        let digit2 = if i < max_len { (s2_norm.index((max_len - 1 - i) as nat) == '1') as u8 } else { 0 };

        let sum = digit1 + digit2 + carry;
        carry = sum / 2;
        let current_digit = sum % 2;

        if current_digit == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }

        i = i + 1;
    }

    proof {
        assert(result_vec@.len() == i);
    }

    let mut reversed_result_vec = Vec::new();
    let mut k: usize = result_vec.len();
    while k > 0
        invariant
            (reversed_result_vec.len() as int) == (result_vec.len() as int) - k as int,
            result_vec@.subrange(k as int, result_vec.len() as int).reverse() == reversed_result_vec@,
        decreases k
    {
        k = k - 1;
        reversed_result_vec.push(result_vec[k]); // Indexing with k as usize
    }

    let cleaned_result_seq = normalize_bit_string(reversed_result_vec@);
    let mut final_result_vec = Vec::new();
    for j in 0..cleaned_result_seq.len() {
        final_result_vec.push(cleaned_result_seq.index(j as nat));
    }

    proof {
        assert(valid_bit_string(final_result_vec@));
    }
    final_result_vec
}
// </vc-code>


}

fn main() {}