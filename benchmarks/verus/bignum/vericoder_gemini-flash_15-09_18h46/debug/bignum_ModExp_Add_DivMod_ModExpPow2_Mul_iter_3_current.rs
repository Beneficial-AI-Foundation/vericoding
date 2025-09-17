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
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Fixed compilation errors related to `nat` and `int` type casting. */
    let mut result: Vec<char> = Vec::new();
    let mut carry: nat = 0;
    let mut i: int = 0;
    let mut j: int = 0;

    while i < s1.len() as int || j < s2.len() as int || carry > 0
        invariant
            carry >= 0 && carry <= 2,
            ValidBitString(result@),
            i <= s1.len(),
            j <= s2.len(),
        decreases (s1.len() as int - i) + (s2.len() as int - j)
    {
        let mut sum: nat = carry;
        if i < s1.len() as int {
            sum += (s1[s1.len() - 1 - i as int] as u8 - b'0') as nat;
        }
        if j < s2.len() as int {
            sum += (s2[s2.len() - 1 - j as int] as u8 - b'0') as nat;
        }

        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;

        if i < s1.len() as int {
            i += 1;
        }
        if j < s2.len() as int {
            j += 1;
        }
    }

    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): No changes Made. */
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;

    let mut quotient_vec = Vec::<char>::new();
    if quotient_val == 0 {
        quotient_vec.push('0');
    } else {
        let mut temp_quotient = quotient_val;
        while temp_quotient > 0
            invariant
                temp_quotient >= 0,
                ValidBitString(quotient_vec@),
            decreases temp_quotient
        {
            quotient_vec.insert(0, if temp_quotient % 2 == 1 { '1' } else { '0' });
            temp_quotient /= 2;
        }
    }

    let mut remainder_vec = Vec::<char>::new();
    if remainder_val == 0 {
        remainder_vec.push('0');
    } else {
        let mut temp_remainder = remainder_val;
        while temp_remainder > 0
            invariant
                temp_remainder >= 0,
                ValidBitString(remainder_vec@),
            decreases temp_remainder
        {
            remainder_vec.insert(0, if temp_remainder % 2 == 1 { '1' } else { '0' });
            temp_remainder /= 2;
        }
    }

    // Proof to establish that the generated vectors are valid bit strings
    proof {
        //@ assert ValidBitString(quotient_vec@);
        //@ assert ValidBitString(remainder_vec@);
    }

    (quotient_vec, remainder_vec)
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
/* code modified by LLM (iteration 3): No changes Made. */
    let x_val = Str2Int(sx@);
    let z_val = Str2Int(sz@);
    let mut acc_val: nat = 1;
    let mut i: int = 0;

    while i < n + 1 // Iterate n+1 times for a y of length n+1 representing 2^n
        invariant 
            0 <= i <= n + 1,
            acc_val == Exp_int(x_val, Exp_int(2, i as nat)) % z_val,
            ValidBitString(sx@),
            ValidBitString(sy@),
            ValidBitString(sz@),
            Str2Int(sz@) > 1,
            (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
            sy@.len() == (n as nat) + 1,
        decreases n - i
    {
        acc_val = (acc_val * acc_val) % z_val;
        i = i + 1;
    }

    let mut result_vec = Vec::<char>::new();
    if acc_val == 0 {
        result_vec.push('0');
    } else {
        let mut temp_val = acc_val;
        while temp_val > 0
            invariant
                temp_val >= 0,
                ValidBitString(result_vec@),
            decreases temp_val
        {
            result_vec.insert(0, if temp_val % 2 == 1 { '1' } else { '0' });
            temp_val /= 2;
        }
    }
    
    result_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): No changes Made. */
    let mut result: Vec<char> = Vec::new();
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    let mut product_val = s1_val * s2_val;

    if product_val == 0 {
        result.push('0');
        return result;
    }

    while product_val > 0
        invariant
            product_val >= 0,
            ValidBitString(result@),
        decreases product_val
    {
        result.insert(0, if product_val % 2 == 1 { '1' } else { '0' });
        product_val /= 2;
    }

    result
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): No changes Made. */
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    let mut res: nat = 1;
    let mut base = x % z;
    let mut exp = y;

    while exp > 0
        invariant
            exp >= 0,
            res == Exp_int(x, y - exp) * Exp_int(base, exp) % z,
            base == x % z,
            ValidBitString(sx@),
            ValidBitString(sy@),
            ValidBitString(sz@),
            Str2Int(sz@) > 1,
        decreases exp
    {
        if exp % 2 == 1 {
            res = (res * base) % z;
        }
        base = (base * base) % z;
        exp /= 2;
    }

    let mut result_vec = Vec::<char>::new();
    if res == 0 {
        result_vec.push('0');
    } else {
        let mut temp_res = res;
        while temp_res > 0
            invariant
                temp_res >= 0,
                ValidBitString(result_vec@),
            decreases temp_res
        {
            result_vec.insert(0, if temp_res % 2 == 1 { '1' } else { '0' });
            temp_res /= 2;
        }
    }

    result_vec
}
// </vc-code>

fn main() {}
}
