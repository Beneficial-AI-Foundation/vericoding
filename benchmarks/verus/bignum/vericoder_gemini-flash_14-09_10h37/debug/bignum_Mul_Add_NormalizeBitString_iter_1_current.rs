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
spec fn CharToInt(c: char) -> nat { if c == '0' { 0nat } else if c == '1' { 1nat } else { 0nat } }
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result_vec = Vec::<char>::new();
    if len1 == 0 || len2 == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let max_len = len1 + len2;
    let mut products: Vec<int> = Vec::new();
    products.resize(max_len + 1, 0);

    for i in 0..len1
        invariant
            0 <= i && i <= len1,
            products.len() == max_len + 1
    {
        let digit1 = CharToInt(s1@[len1 - 1 - i]) as int;
        for j in 0..len2
            invariant
                0 <= j && j <= len2,
                products.len() == max_len + 1
        {
            let digit2 = CharToInt(s2@[len2 - 1 - j]) as int;
            let product = digit1 * digit2;
            products.set(i + j, products.index(i + j) + product);
        }
    }

    let mut carry = 0;
    for i in 0..max_len
        invariant
            0 <= i && i <= max_len,
            products.len() == max_len + 1,
            0 <= carry
    {
        let sum = products.index(i) + carry;
        products.set(i, sum % 2);
        carry = sum / 2;
    }
    products.set(max_len, products.index(max_len) + carry);

    let mut started = false;
    for i in (0..=max_len).rev()
        invariant
            0 <= i + 1 && i + 1 <= max_len + 1,
            ({ let product_vec_len = result_vec.len();
                if started { product_vec_len == max_len - i } else { true } })
    {
        if products.index(i) == 1 {
            started = true;
            result_vec.push('1');
        } else if started {
            result_vec.push('0');
        }
    }

    if !started {
        result_vec.push('0');
    }

    result_vec
}
// </vc-code>

fn main() {}
}
