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
    let dividend_seq = dividend@;
    let mut quotient = Vec::new();
    let mut remainder = 0nat;
    let str_divisor = Str2Int(divisor@);
    let mut i = 0;
    while i < dividend_seq.len()
        invariant
            0 <= i <= dividend_seq.len(),
            remainder < str_divisor,
        decreases dividend_seq.len() - i
    {
        let bit = if dividend_seq[i] == '1' {1nat} else {0nat};
        let remainder_new = 2 * remainder + bit;
        let add_bit;
        if remainder_new >= str_divisor {
            add_bit = '1';
            remainder = remainder_new - str_divisor;
        } else {
            add_bit = '0';
            remainder = remainder_new;
        }
        quotient.push(add_bit);
        i += 1;
    }
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
    }
    let mut remainder_bits = Vec::new();
    if remainder == 0nat {
        remainder_bits.push('0');
    } else {
        while remainder > 0 {
            if remainder % 2 == 1 {
                remainder_bits.push('1');
            } else {
                remainder_bits.push('0');
            }
            remainder = remainder / 2;
        }
        remainder_bits.reverse();
    }
    (quotient, remainder_bits)
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
    let str_x = Str2Int(sx@);
    let str_y = Str2Int(sy@);
    if str_y == 0 {
        return vec!['1'];
    } else {
        let str_z = Str2Int(sz@);
        let mut result = 1nat;
        let mut i = 0;
        while i < (n as nat) + 1
            invariant
                0 <= i <= (n as nat) + 1,
                0 <= result < str_z,
            decreases (n as nat) + 1 - i
        {
            result = (result * result) % str_z;
            if sy@[i] == '1' {
                result = (result * str_x) % str_z;
            }
            i += 1;
        }
        let mut result_bits = Vec::new();
        if result == 0nat {
            result_bits.push('0');
        } else {
            while result > 0 {
                if result % 2 == 1 {
                    result_bits.push('1');
                } else {
                    result_bits.push('0');
                }
                result = result / 2;
            }
            result_bits.reverse();
        }
        return result_bits;
    }
}
// </vc-code>

fn main() {}
}


