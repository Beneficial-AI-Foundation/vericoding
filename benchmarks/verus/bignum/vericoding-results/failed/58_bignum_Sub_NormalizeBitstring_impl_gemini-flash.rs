// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `int` suffix from integer literals to fix compilation error. */
fn sub_digit_with_borrow(d1: char, d2: char, borrow_in: char) -> (res: (char, char))
  requires
    d1 == '0' || d1 == '1',
    d2 == '0' || d2 == '1',
    borrow_in == '0' || borrow_in == '1'
  ensures
    res.0 == '0' || res.0 == '1',
    res.1 == '0' || res.1 == '1'
{
  let d1_int: int = if d1 == '1' { 1 } else { 0 };
  let d2_int: int = if d2 == '1' { 1 } else { 0 };
  let borrow_in_int: int = if borrow_in == '1' { 1 } else { 0 };

  let mut result_int = d1_int - d2_int - borrow_in_int;
  let mut borrow_out = '0';

  if result_int < 0 {
    result_int = result_int + 2;
    borrow_out = '1';
  }

  let result_char = if result_int == 1 { '1' } else { '0' };

  (result_char, borrow_out)
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@) &&
    str2int(s1@) >= str2int(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) - str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed `assume(false)` and `unreached()` statements. Added an explicit `assert` to show the string conversion. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut borrow: char = '0';

    let s1_len = s1.len();
    let s2_len = s2.len();
    let common_len = if s1_len > s2_len { s1_len } else { s2_len };

    let mut i: usize = 0;
    while i < common_len
        invariant
            0 <= i as int,
            valid_bit_string(result_vec@),
            borrow == '0' || borrow == '1',
            i <= common_len
        decreases common_len - i
    {
        let d1_char: char = if i < s1_len { s1[s1_len - 1 - i] } else { '0' };
        let d2_char: char = if i < s2_len { s2[s2_len - 1 - i] } else { '0' };
        
        let (digit_res, next_borrow) = sub_digit_with_borrow(d1_char, d2_char, borrow);
        result_vec.push(digit_res);
        borrow = next_borrow;
        i = i + 1;
    }

    let mut final_result_vec: Vec<char> = Vec::new();
    let mut leading_zeros: bool = true;

    while result_vec.len() > 0
        invariant
            valid_bit_string(final_result_vec@),
            valid_bit_string(result_vec@)
        decreases result_vec.len()
    {
        let digit = result_vec.pop().unwrap();
        if leading_zeros && digit == '0' && result_vec.len() > 0 {
            // Skip leading zeros unless it's the only remaining digit and it's 0
        } else {
            leading_zeros = false;
            final_result_vec.push(digit);
        }
    }

    if final_result_vec.len() == 0 {
        vec!['0']
    } else {
        assert(final_result_vec@.len() > 0);
        final_result_vec
    }
}
// </vc-code>


}

fn main() {}