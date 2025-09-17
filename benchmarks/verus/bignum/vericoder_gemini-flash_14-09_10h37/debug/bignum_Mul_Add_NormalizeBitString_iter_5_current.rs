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
/* helper modified by LLM (iteration 5): Corrected return types to `nat` literals instead of `int`. */
exec fn char_to_nat(c: char) -> (val: nat) {
    if c == '0' {
        0 nat
    } else if c == '1' {
        1 nat
    } else {
        0 nat // Should not happen given the ValidBitString precondition
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches by ensuring all numeric literals and calculations involving `nat` types are explicitly `nat`. Also addressed the Verus internal error regarding `for` loop iteration over `std::iter::Rev`. */{
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    let mut result_vec = Vec::<char>::new();
    if len1 == 0 || len2 == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let max_len: usize = len1 + len2;
    let mut products: Vec<nat> = Vec::new();
    products.resize(max_len + 1, 0 nat);

    for i in 0..len1
        invariant
            0 <= i && i <= len1,
            products.len() == max_len + 1,
    {
        let digit1 = char_to_nat(s1[len1 - 1 - i]);
        for j in 0..len2
            invariant
                0 <= j && j <= len2,
                products.len() == max_len + 1
        {
            let digit2 = char_to_nat(s2[len2 - 1 - j]);
            let product: nat = digit1 * digit2;
            let current_val: nat = products[i + j];
            products.set(i + j, current_val + product);
        }
    }

    let mut carry: nat = 0 nat;
    for i in 0..max_len
        invariant
            0 <= i && i <= max_len,
            products.len() == max_len + 1,
            0 <= carry
    {
        let sum: nat = products[i] + carry;
        products.set(i, sum % 2 nat);
        carry = sum / 2 nat;
    }
    products.set(max_len, products[max_len] + carry);

    let mut started = false;
    // Verus does not support `rev()` for `RangeInclusive` in `for` loops directly.
    // Iterate forwards and then reverse the characters at the end.
    let mut temp_chars: Vec<char> = Vec::new();

    for i in (0..=max_len) {
        if products[max_len - i] == 1 nat {
            started = true;
            temp_chars.push('1');
        } else if started {
            temp_chars.push('0');
        }
    }

    if !started {
        result_vec.push('0');
    } else {
        for i in (0..temp_chars.len()) {
            result_vec.push(temp_chars[temp_chars.len() - 1 - i]);
        }
    }

    result_vec
}
// </vc-code>

fn main() {}
}
