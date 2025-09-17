use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 7): Corrected return type syntax */
spec fn AddBitStringsDigit(a_digit: char, b_digit: char, carry_in: nat) -> (sum_digit: char, carry_out: nat)
    requires
        (a_digit == '0' || a_digit == '1'),
        (b_digit == '0' || b_digit == '1'),
        (carry_in == 0 || carry_in == 1)
    ensures
        (sum_digit == '0' || sum_digit == '1'),
        (carry_out == 0 || carry_out == 1)
{
    let a_int = if a_digit == '1' { 1 } else { 0 };
    let b_int = if b_digit == '1' { 1 } else { 0 };
    let sum_val = (a_int + b_int + carry_in) as nat;
    let sum_digit = if sum_val % 2 == 1 { '1' } else { '0' };
    let carry_out = sum_val / 2;
    (sum_digit, carry_out)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Changed `max_len` calculation and loop termination condition. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let a_seq = a@;
    let b_seq = b@;

    let len_a = a_seq.len();
    let len_b = b_seq.len();
    let mut carry: nat = 0;
    let mut i: int = 0;

    while i < len_a || i < len_b || carry == 1
        invariant
            carry == 0 || carry == 1,
            i >= 0,
            ValidBitString(result_vec@),
    {
        let a_digit = if i < len_a { a_seq.index(len_a - 1 - i) } else { '0' };
        let b_digit = if i < len_b { b_seq.index(len_b - 1 - i) } else { '0' };

        let (sum_digit, new_carry) = AddBitStringsDigit(a_digit, b_digit, carry);
        result_vec.insert(0, sum_digit);
        carry = new_carry;
        i = i + 1;
    }

    if result_vec.len() == 0 {
        result_vec.push('0');
    }
    result_vec
}
// </vc-code>

fn main() {}
}

