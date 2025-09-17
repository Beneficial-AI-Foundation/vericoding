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
proof fn lemma_sub_digits_valid(c1: char, c2: char, borrow_in: nat) -> (ok: bool, diff_digit: char, borrow_out: nat)
    requires
        (c1 == '0' || c1 == '1'),
        (c2 == '0' || c2 == '1'),
        (borrow_in == 0 || borrow_in == 1),
        (if borrow_in == 1 { Str2Int(seq![c1]) } else { Str2Int(seq![c1]) }) >= Str2Int(seq![c2])
    ensures
        ok == true,
        (diff_digit == '0' || diff_digit == '1'),
        (borrow_out == 0 || borrow_out == 1),
        Str2Int(seq![diff_digit]) + borrow_out * 2 == (if borrow_in == 1 { Str2Int(seq![c1]) } else { Str2Int(seq![c1]) }) - Str2Int(seq![c2])
{
    let d1 = if c1 == '1' { 1 } else { 0 };
    let d2 = if c2 == '1' { 1 } else { 0 };

    let val1 = if borrow_in == 1 { d1 + 2 } else { d1 };

    let diff = val1 - d2;

    let digit = if diff == 1 { '1' } else { '0' };
    let new_borrow = 0;

    (true, digit, new_borrow)
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = s1.len();
    let n2 = s2.len();
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0;

    let mut i: int = 0;
    while i < n1
        invariant
            0 <= i,
            i <= n1,
            carry == 0 || carry == 1,
            ValidBitString(result_vec@),
            Str2Int(s1@.subrange(0, i)) == Str2Int(s2@.subrange(0, i)) + Str2Int(result_vec@) + carry * (1 << i),
    {
        let d1_char = s1[n1 as int - 1 - i];
        let d2_char = if i < n2 { s2[n2 as int - 1 - i] } else { '0' };

        let d1_val = if d1_char == '1' { 1 } else { 0 };
        let d2_val = if d2_char == '1' { 1 } else { 0 };

        let val_with_borrow = d1_val - carry;

        let diff_val: int;
        let new_carry: nat;

        if val_with_borrow >= d2_val {
            diff_val = val_with_borrow - d2_val;
            new_carry = 0;
        } else {
            diff_val = val_with_borrow - d2_val + 2;
            new_carry = 1;
        }

        let diff_char = if diff_val == 1 { '1' } else { '0' };
        result_vec.push(diff_char);
        carry = new_carry;
        i = i + 1;
    }

    result_vec.reverse();

    // Remove leading zeros, unless the result is just '0'
    let mut first_one = 0;
    while first_one < result_vec.len() - 1 && result_vec[first_one] == '0'
        invariant
            0 <= first_one,
            first_one < result_vec.len(),
            result_vec.len() >= 1,
            forall |j: int| 0 <= j < first_one ==> result_vec[j] == '0',
            result_vec[first_one] == '0'
    {
        first_one = first_one + 1;
    }

    let final_result = result_vec.subslice(first_one as usize, result_vec.len() - first_one);
    final_result.to_vec()
}
// </vc-code>

fn main() {}
}


