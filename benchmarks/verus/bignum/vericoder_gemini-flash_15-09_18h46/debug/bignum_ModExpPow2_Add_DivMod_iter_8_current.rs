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
/* code modified by LLM (iteration 8): Added `as nat` casts for integer literals where `nat` is expected. */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0; // Fixed: Added `as nat` cast for 0
    let mut i: usize = 0;

    while i < max_len || carry > (0 as nat)
        invariant
            0 <= i as int,
            result_vec.len() == i,
            carry == (0 as nat) || carry == (1 as nat),
            ValidBitString(result_vec@)
        decreases max_len + 1 - i
    {
        let digit1_val: nat = if i < len1 && (s1[len1 - 1 - i] == '1') { 1 as nat } else { 0 as nat }; // Fixed: Added `as nat` casts for 1 and 0
        let digit2_val: nat = if i < len2 && (s2[len2 - 1 - i] == '1') { 1 as nat } else { 0 as nat }; // Fixed: Added `as nat` casts for 1 and 0

        let sum = digit1_val + digit2_val + carry;
        let current_digit = sum % 2;
        carry = sum / 2;

        result_vec.insert(0, if current_digit == (1 as nat) { '1' } else { '0' });
        i = i + 1;
    }

    if result_vec.is_empty() {
        result_vec.push('0');
    }
    result_vec
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
/* code modified by LLM (iteration 8): Added `as nat` casts for integer literals where `nat` is expected. */
{
    if Str2Int(dividend@) < Str2Int(divisor@) {
        let mut vec_dividend = Vec::new();
        let mut i: usize = 0;
        while i < dividend.len()
            invariant
                0 <= i,
                i <= dividend.len(),
                vec_dividend.len() == i,
                ValidBitString(vec_dividend@)
            decreases dividend.len() - i
        {
            vec_dividend.push(dividend[i as usize]);
            i = i + 1;
        }
        return (vec!['0'], vec_dividend);
    }

    let nat_dividend = Str2Int(dividend@);
    let nat_divisor = Str2Int(divisor@);

    let nat_quotient = nat_dividend / nat_divisor;
    let nat_remainder = nat_dividend % nat_divisor;

    let mut quotient_vec: Vec<char> = Vec::new();
    let mut q: nat = nat_quotient;

    if q == (0 as nat) { // Fixed: Added `as nat` cast
        quotient_vec.push('0');
    } else {
        while q > (0 as nat) // Fixed: Added `as nat` cast
            invariant
                ValidBitString(quotient_vec@),
                q < nat_quotient + (1 as nat) // Fixed: Added `as nat` cast
            decreases q
        {
            if q % (2 as nat) == (1 as nat) { // Fixed: Added `as nat` casts
                quotient_vec.insert(0, '1');
            } else {
                quotient_vec.insert(0, '0');
            }
            q = q / (2 as nat); // Fixed: Added `as nat` cast
        }
    }

    let mut remainder_vec: Vec<char> = Vec::new();
    let mut r: nat = nat_remainder;

    if r == (0 as nat) { // Fixed: Added `as nat` cast
        remainder_vec.push('0');
    } else {
        while r > (0 as nat) // Fixed: Added `as nat` cast
            invariant
                ValidBitString(remainder_vec@),
                r < nat_remainder + (1 as nat) // Fixed: Added `as nat` cast
            decreases r
        {
            if r % (2 as nat) == (1 as nat) { // Fixed: Added `as nat` casts
                remainder_vec.insert(0, '1');
            } else {
                remainder_vec.insert(0, '0');
            }
            r = r / (2 as nat); // Fixed: Added `as nat` cast
        }
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
/* code modified by LLM (iteration 8): Added `as nat` casts for integer literals where `nat` is expected. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let mut result_nat: nat = 1 as nat; // Fixed: Added `as nat` cast
    let mut base: nat = x_int % z_int;
    let mut exp: nat = y_int;

    while exp > (0 as nat) // Fixed: Added `as nat` cast
        invariant
            result_nat >= (0 as nat),
            base >= (0 as nat),
            exp >= (0 as nat),
            z_int > (0 as nat),
        decreases exp
    {
        if exp % (2 as nat) == (1 as nat) { // Fixed: Added `as nat` casts
            result_nat = (result_nat * base) % z_int;
        }
        base = (base * base) % z_int;
        exp = exp / (2 as nat); // Fixed: Added `as nat` cast
    }

    let mut result_vec: Vec<char> = Vec::new();
    let mut temp: nat = result_nat;

    if temp == (0 as nat) { // Fixed: Added `as nat` cast
        result_vec.push('0');
    } else {
        while temp > (0 as nat) // Fixed: Added `as nat` cast
            invariant
                ValidBitString(result_vec@),
                temp < result_nat + (1 as nat) // Fixed: Added `as nat` cast
            decreases temp
        {
            if temp % (2 as nat) == (1 as nat) { // Fixed: Added `as nat` casts
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp = temp / (2 as nat); // Fixed: Added `as nat` cast
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}


