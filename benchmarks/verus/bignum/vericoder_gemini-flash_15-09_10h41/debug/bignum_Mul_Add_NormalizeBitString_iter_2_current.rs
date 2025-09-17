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
/* helper modified by LLM (iteration 2): add comments */
spec fn CharToNat(c: char) -> nat ensures (c == '0' ==> result == 0) && (c == '1' ==> result == 1) { if c == '0' { 0nat } else { 1nat } 
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix type errors for `nat`/`int` and undefined variables. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut k: int = 0;

    let s1_seq = s1@;
    let s2_seq = s2@;

    if s1_seq.len() == 0 || s2_seq.len() == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let n1: int = s1_seq.len() as int;
    let n2: int = s2_seq.len() as int;
    let mut products: Vec<Vec<char>> = Vec::new();

    // Simulate multiplication of each digit of s2 with s1
    while k < n2
        invariant
            0 <= k,
            k <= n2,
            products.len() == k,
            forall |i: int| 0 <= i && i < products.len() ==> ValidBitString(products.view_at(i)@)
        decreases n2 - k
    {
        let digit2 = CharToNat(s2_seq.index(n2 - 1 - k));
        let mut current_product_vec: Vec<char> = Vec::new();
        let mut current_carry: nat = 0;
        let mut j: int = 0;

        // Append k zeros for position alignment
        while j < k
            invariant
                0 <= j,
                j <= k,
                ValidBitString(current_product_vec@)
            decreases k - j
        {
            current_product_vec.push('0');
            j = j + 1;
        }

        // Multiply s1 by digit2
        j = 0;
        while j < n1
            invariant
                0 <= j,
                j <= n1,
                current_carry < 2,
                ValidBitString(current_product_vec@)
            decreases n1 - j
        {
            let digit1 = CharToNat(s1_seq.index(n1 - 1 - j));
            let prod = digit1 * digit2 + current_carry;
            current_product_vec.push(if (prod % 2) == 0 { '0' } else { '1' });
            current_carry = prod / 2;
            j = j + 1;
        }

        if current_carry > 0 {
            current_product_vec.push(if current_carry == 1 { '1' } else { '0' });
        }
        products.push(current_product_vec);
        k = k + 1;
    }

    // Sum the partial products
    let mut max_len: int = 0;
    if products.len() > 0 {
        max_len = products.view_at(products.len() as int - 1)@.len()
            + (products.len() as int - 1) + 1; // Worst case length
    }

    let mut sum_result: Seq<nat> = Seq::new();
    k = 0;
    let mut current_carry: nat = 0;
    while k < max_len + 1
        invariant
            0 <= k,
            current_carry < 2,
            sum_result.len() == k,
            // @todo: Add invariant for ValidBitString on partial products in `products`
        decreases max_len + 1 - k
    {
        let mut current_sum_digit: nat = current_carry;
        let mut i: int = 0;
        while i < products.len()
            invariant
                0 <= i,
                i <= products.len(),
                current_sum_digit >= current_carry,
                forall |idx: int| 0 <= idx && idx < products.len() ==> ValidBitString(products.view_at(idx)@)
            decreases products.len() - i
        {
            let prod_seq = products.view_at(i)@;
            if k < prod_seq.len() {
                current_sum_digit = current_sum_digit + CharToNat(prod_seq.index(k));
            }
            i = i + 1;
        }
        
        sum_result = sum_result.push(current_sum_digit % 2);
        current_carry = current_sum_digit / 2;
        k = k + 1;
    }

    // Convert the sum_result to Vec<char>
    let mut final_vec: Vec<char> = Vec::new();
    let mut leading_zeros = true;
    let mut l: int = sum_result.len() as int - 1;

    while l >= 0
        invariant
            -1 <= l,
            l < sum_result.len() as int,
            ValidBitString(final_vec@)
        decreases l
    {
        let digit = sum_result.index(l);
        if leading_zeros && digit == 0 && l > 0 {
            // Skip leading zeros unless it's the last digit and it's 0 (meaning the result is 0)
        } else {
            leading_zeros = false;
            final_vec.push(if digit == 0 { '0' } else { '1' });
        }
        l = l - 1;
    }

    if final_vec.len() == 0 {
        final_vec.push('0');
    }

    final_vec
}
// </vc-code>

fn main() {}
}
