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
/* helper modified by LLM (iteration 4): Renamed `CharToInt` to `char_to_nat` and made it an `exec` function to be called from `exec` functions. */
exec fn char_to_nat(c: char) -> (val: nat) {
    if c == '0' {
        0
    } else if c == '1' {
        1
    } else {
        0 // Should not happen given the ValidBitString precondition
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed numerous compilation errors including type mismatches related to `usize` vs `nat`, indexing issues with `Seq` instead of `&[char]`, and incorrect use of `products.index` which should be `products[index]` or `products.get(index)`. Also, fixed the `products.resize` argument order, and the `for` loop ranges to use `usize`. */{
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    let mut result_vec = Vec::<char>::new();
    if len1 == 0 || len2 == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let max_len: usize = len1 + len2;
    let mut products: Vec<nat> = Vec::new();
    // Corrected `resize` arguments: first size, then default value
    products.resize(max_len + 1, 0);

    for i in 0..len1
        invariant
            0 <= i && i <= len1,
            products.len() == max_len + 1,
            // ghost forall |k: int| 0 <= k < products.len() ==> products[k] >= 0
    {
        // s1 is &[char], direct indexing is allowed
        let digit1 = char_to_nat(s1[len1 - 1 - i]);
        for j in 0..len2
            invariant
                0 <= j && j <= len2,
                products.len() == max_len + 1
                            // ghost forall |k: int| 0 <= k < products.len() ==> products[k] >= 0

        {
            // s2 is &[char], direct indexing is allowed
            let digit2 = char_to_nat(s2[len2 - 1 - j]);
            let product: nat = digit1 * digit2;
            // Direct indexing with `[]` on Vec is allowed for `exec` code.
            // We need to unwrap the option returned by get.
            let current_val = products[i + j];
            products.set(i + j, current_val + product);
        }
    }

    let mut carry: nat = 0;
    for i in 0..max_len
        invariant
            0 <= i && i <= max_len,
            products.len() == max_len + 1,
            0 <= carry
          
            // ghost forall |k: int| 0 <= k < i ==> 0 <= products[k] < 2


    {
        // Direct indexing with `[]` on Vec is allowed.
        let sum: nat = products[i] + carry;
        products.set(i, sum % 2);
        carry = sum / 2;
    }
    products.set(max_len, products[max_len] + carry);

    let mut started = false;
    for i in (0..=max_len).rev() // i is usize here
        invariant
            // Need to convert `i` to `int` for logical operations
            // `i` is current value in the loop, so `i+1` is valid `len` type
            (i as int) + 1 >= 0 && (i as int) + 1 <= (max_len as int) + 1,
            ({ // Predicate on product_vec_len removed to simplify invariant temporarily
                true
            })
    {
        if products[i] == 1 {
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
