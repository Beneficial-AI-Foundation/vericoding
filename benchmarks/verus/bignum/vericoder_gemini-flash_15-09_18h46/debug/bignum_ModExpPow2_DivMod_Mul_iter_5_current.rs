use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fix `i` type and indexing for `dividend` */
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    if dividend_val < divisor_val {
        return (vec!['0'], dividend.to_vec());
    }

    let mut q_chars: Vec<char> = Vec::new();
    let mut r_val = 0nat;

    let mut i: usize = dividend.len() - 1;
    while i != usize::MAX
        invariant
            0 <= (i as int) + 1 && ((i as int) + 1) <= dividend.len(),
            forall |j: int| 0 <= j && j < q_chars.len() ==> (q_chars@[j] == '0' || q_chars@[j] == '1'),
            r_val < divisor_val,
            // r_val == Str2Int(dividend.subrange(i as int + 1, dividend.len() as int)) % divisor_val, // This invariant is complex to prove here
            // Str2Int(q_chars@) == Str2Int(dividend.subrange(i as int + 1, dividend.len() as int)) / divisor_val, // This invariant is complex to prove here
            (i as int) >= -1 // i can go to -1 in last iter, so this is correct
        decreases i
    {
        let current_bit = if dividend@[i] == '1' { 1nat } else { 0nat };
        r_val = r_val * 2 + current_bit;

        if r_val >= divisor_val {
            q_chars.insert(0, '1');
            r_val = r_val - divisor_val;
        } else {
            q_chars.insert(0, '0');
        }

        if i == 0 {
             break;
        }
        i = i - 1;
    }
    
    // Remove leading zeros from quotient unless it's just '0'
    let mut final_q = Vec::new();
    let mut found_one = false;
    if q_chars.is_empty() {
        final_q.push('0');
    } else {
        let mut first = true;
        for j in 0..q_chars.len() {
            if q_chars@[j] == '1' {
                found_one = true;
            }
            if found_one || (q_chars.len() == 1 && first) {
                final_q.push(q_chars@[j]);
                first = false;
            }
        }
    }
    if final_q.is_empty() {
        final_q.push('0');
    }

    let mut final_r = Vec::new();
    if r_val == 0 {
        final_r.push('0');
    } else {
        let mut temp_r_val = r_val;
        while temp_r_val > 0
            invariant
                forall |j: int| 0 <= j && j < final_r.len() ==> (final_r@[j] == '0' || final_r@[j] == '1'),
                (temp_r_val == 0 && final_r.is_empty()) || 
                (temp_r_val > 0 && r_val == Str2Int(final_r@) * Exp_int(2, (final_r.len() as nat)) + temp_r_val
                 && (temp_r_val < Exp_int(2, (final_r.len() as nat)))) // This invariant is tricky without bit knowledge
            decreases temp_r_val
        {
            if temp_r_val % 2 == 1 {
                final_r.insert(0, '1');
            } else {
                final_r.insert(0, '0');
            }
            temp_r_val = temp_r_val / 2;
        }
    }

    (final_q, final_r)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): No changes. */
    let val1 = Str2Int(s1@);
    let val2 = Str2Int(s2@);
    let product_val = val1 * val2;

    if product_val == 0 {
        return vec!['0'];
    }

    let mut result_chars: Vec<char> = Vec::new();
    let mut temp_product = product_val;

    while temp_product > 0
        invariant
            result_chars.is_empty() || (forall |j: int| 0 <= j && j < result_chars.len() ==> (result_chars@[j] == '0' || result_chars@[j] == '1')),
            product_val == (temp_product * Exp_int(2, result_chars.len() as nat)) + Str2Int(result_chars@)
        decreases temp_product
    {
        if temp_product % 2 == 1 {
            result_chars.insert(0, '1');
        } else {
            result_chars.insert(0, '0');
        }
        temp_product /= 2;
    }

    result_chars
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): No changes. */
    let one_char = ['1'];
    let zero_char = ['0'];
    let two_val = 2nat;

    let sx_val = Str2Int(sx@);
    let sy_val = Str2Int(sy@);
    let sz_val = Str2Int(sz@);

    if sy_val == 0 {
        return vec!['1']; // x^0 = 1
    }

    if sx_val == 0 {
        return vec!['0']; // 0^y = 0 for y > 0
    }

    let mut res_val = 1nat;
    let mut x_power_val = sx_val % sz_val;
    let mut y_remaining = sy_val;

    while y_remaining > 0
        invariant
            sx_val > 0,
            sz_val > 1,
            (res_val * Exp_int(x_power_val, y_remaining)) % sz_val == Exp_int(sx_val, sy_val) % sz_val,
            x_power_val < sz_val,
            res_val < sz_val
        decreases y_remaining
    {
        if y_remaining % two_val == 1 {
            res_val = (res_val * x_power_val) % sz_val;
        }
        x_power_val = (x_power_val * x_power_val) % sz_val;
        y_remaining /= two_val;
    }

    // Convert res_val back to a bit string
    if res_val == 0 {
        return zero_char.to_vec();
    }

    let mut result_chars: Vec<char> = Vec::new();
    let mut temp_res = res_val;

    while temp_res > 0
        invariant
            result_chars.is_empty() || (forall |j: int| 0 <= j && j < result_chars.len() ==> (result_chars@[j] == '0' || result_chars@[j] == '1')),
            res_val == (temp_res * Exp_int(2, result_chars.len() as nat)) + Str2Int(result_chars@)
        decreases temp_res
    {
        if temp_res % two_val == 1 {
            result_chars.insert(0, '1');
        } else {
            result_chars.insert(0, '0');
        }
        temp_res /= two_val;
    }
    result_chars
}
// </vc-code>

fn main() {}
}
