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
    let mut i = s1.len() as int - 1;
    let mut j = s2.len() as int - 1;
    let mut carry = 0;
    let mut res_vec = Vec::new();

    while i >= 0 || j >= 0 || carry > 0
        invariant
            carry == 0 || carry == 1,
        decreases (i+1) + (j+1) + carry
    {
        let bit1 = if i >= 0 { s1[i] } else { '0' };
        let bit2 = if j >= 0 { s2[j] } else { '0' };
        let sum = (if bit1 == '1' { 1 } else { 0 }) + (if bit2 == '1' { 1 } else { 0 }) + carry;
        let current_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        res_vec.push(current_bit);
        if i >= 0 { i -= 1; }
        if j >= 0 { j -= 1; }
    }

    res_vec.reverse();
    res_vec
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
    // Convert dividend to nat
    let mut num1 = 0;
    let mut i = 0;
    while i < dividend.len()
        invariant
            num1 == Str2Int(dividend@.subrange(0, i)),
            i <= dividend.len()
        decreases dividend.len() - i
    {
        num1 = num1 * 2 + (if dividend[i] == '1' { 1 } else { 0 });
        i += 1;
    }

    // Convert divisor to nat
    let mut num2 = 0;
    let mut j = 0;
    while j < divisor.len()
        invariant
            num2 == Str2Int(divisor@.subrange(0, j)),
            j <= divisor.len()
        decreases divisor.len() - j
    {
        num2 = num2 * 2 + (if divisor[j] == '1' { 1 } else { 0 });
        j += 1;
    }

    let quotient = num1 / num2;
    let remainder = num1 % num2;

    // Convert quotient to binary string
    let mut res_quotient = Vec::new();
    if quotient == 0 {
        res_quotient.push('0');
    } else {
        let mut n = quotient;
        while n > 0
            decreases n
        {
            let bit = if n % 2 == 1 { '1' } else { '0' };
            res_quotient.push(bit);
            n = n / 2;
        }
        res_quotient.reverse();
    }

    // Convert remainder to binary string
    let mut res_remainder = Vec::new();
    if remainder == 0 {
        res_remainder.push('0');
    } else {
        let mut n = remainder;
        while n > 0
            decreases n
        {
            let bit = if n % 2 == 1 { '1' } else { '0' };
            res_remainder.push(bit);
            n = n / 2;
        }
        res_remainder.reverse();
    }

    (res_quotient, res_remainder)
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
    // Convert sx to nat
    let mut x = 0;
    let mut i = 0;
    while i < sx.len()
        invariant
            x == Str2Int(sx@.subrange(0, i)),
            i <= sx.len()
        decreases sx.len() - i
    {
        x = x * 2 + (if sx[i] == '1' { 1 } else { 0 });
        i += 1;
    }

    // Convert sy to nat
    let mut y = 0;
    let mut j = 0;
    while j < sy.len()
        invariant
            y == Str2Int(sy@.subrange(0, j)),
            j <= sy.len()
        decreases sy.len() - j
    {
        y = y * 2 + (if sy[j] == '1' { 1 } else { 0 });
        j += 1;
    }

    // Convert sz to nat
    let mut z = 0;
    let mut k = 0;
    while k < sz.len()
        invariant
            z == Str2Int(sz@.subrange(0, k)),
            k <= sz.len()
        decreases sz.len() - k
    {
        z = z * 2 + (if sz[k] == '1' { 1 } else { 0 });
        k += 1;
    }

    let mut result;
    if y == 0 {
        result = 1 % z;
    } else {
        let mut base = x % z;
        let mut count = 0;
        while count < n
            invariant
                base == Exp_int(x, Exp_int(2, count as nat)) % z,
                count <= n
            decreases n - count
        {
            base = (base * base) % z;
            count += 1;
        }
        result = base;
    }

    // Convert result to binary string
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut n_val = result;
        while n_val > 0
            decreases n_val
        {
            let bit = if n_val % 2 == 1 { '1' } else { '0' };
            res_vec.push(bit);
            n_val = n_val / 2;
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Convert s1 to nat
    let mut num1 = 0;
    let mut i = 0;
    while i < s1.len()
        invariant
            num1 == Str2Int(s1@.subrange(0, i)),
            i <= s1.len()
        decreases s1.len() - i
    {
        num1 = num1 * 2 + (if s1[i] == '1' { 1 } else { 0 });
        i += 1;
    }

    // Convert s2 to nat
    let mut num2 = 0;
    let mut j = 0;
    while j < s2.len()
        invariant
            num2 == Str2Int(s2@.subrange(0, j)),
            j <= s2.len()
        decreases s2.len() - j
    {
        num2 = num2 * 2 + (if s2[j] == '1' { 1 } else { 0 });
        j += 1;
    }

    let product = num1 * num2;

    // Convert product to binary string
    let mut res_vec = Vec::new();
    if product == 0 {
        res_vec.push('0');
    } else {
        let mut n = product;
        while n > 0
            decreases n
        {
            let bit = if n % 2 == 1 { '1' } else { '0' };
            res_vec.push(bit);
            n = n / 2;
        }
        res_vec.reverse();
    }

    res_vec
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
    // Convert sx to nat
    let mut x = 0;
    let mut i = 0;
    while i < sx.len()
        invariant
            x == Str2Int(sx@.subrange(0, i)),
            i <= sx.len()
        decreases sx.len() - i
    {
        x = x * 2 + (if sx[i] == '1' { 1 } else { 0 });
        i += 1;
    }

    // Convert sy to nat
    let mut y = 0;
    let mut j = 0;
    while j < sy.len()
        invariant
            y == Str2Int(sy@.subrange(0, j)),
            j <= sy.len()
        decreases sy.len() - j
    {
        y = y * 2 + (if sy[j] == '1' { 1 } else { 0 });
        j += 1;
    }

    // Convert sz to nat
    let mut z = 0;
    let mut k = 0;
    while k < sz.len()
        invariant
            z == Str2Int(sz@.subrange(0, k)),
            k <= sz.len()
        decreases sz.len() - k
    {
        z = z * 2 + (if sz[k] == '1' { 1 } else { 0 });
        k += 1;
    }

    let mut result = 1;
    let mut base = x % z;
    let mut exponent = y;

    while exponent > 0
        invariant
            (result * Exp_int(base, exponent as nat)) % z == Exp_int(x, y) % z,
            base < z,
            result < z,
            exponent <= y
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exponent = exponent / 2;
    }

    // Convert result to binary string
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut n_val = result;
        while n_val > 0
            decreases n_val
        {
            let bit = if n_val % 2 == 1 { '1' } else { '0' };
            res_vec.push(bit);
            n_val = n_val / 2;
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

fn main() {}
}
