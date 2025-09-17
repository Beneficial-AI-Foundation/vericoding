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
/* code modified by LLM (iteration 4): fixed unsupported iter().rev() by using while loop */ {
    fn compute_str_to_nat(s: &[char]) -> u128 {
        let mut res: u128 = 0;
        let mut pos = s.len();
        while pos > 0 {
            pos -= 1;
            res = (res << 1) | if s[pos] == '1' { 1 } else { 0 };
        }
        res
    }
    fn nat_to_bits(nn: u128) -> Vec<char> {
        if nn == 0 {
            return vec!['0'];
        }
        let mut res = Vec::new();
        let mut n = nn;
        while n > 0 {
            res.push(if n % 2 == 0 { '0' } else { '1' });
            n = n >> 1;
        }
        res.reverse();
        res
    }
    let a = compute_str_to_nat(s1);
    let b = compute_str_to_nat(s2);
    let sum = a.wrapping_add(b);
    nat_to_bits(sum)
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
/* code modified by LLM (iteration 4): fixed unsupported iter().rev() by using while loop */ {
    fn compute_str_to_nat(s: &[char]) -> u128 {
        let mut res: u128 = 0;
        let mut pos = s.len();
        while pos > 0 {
            pos -= 1;
            res = (res << 1) | if s[pos] == '1' { 1 } else { 0 };
        }
        res
    }
    fn nat_to_bits(nn: u128) -> Vec<char> {
        if nn == 0 {
            return vec!['0'];
        }
        let mut res = Vec::new();
        let mut n = nn;
        while n > 0 {
            res.push(if n % 2 == 0 { '0' } else { '1' });
            n = n >> 1;
        }
        res.reverse();
        res
    }
    let dividend_num = compute_str_to_nat(dividend);
    let divisor_num = compute_str_to_nat(divisor);
    if divisor_num == 0 {
        (vec!['0'], vec!['0']) // Though requires divisor > 0
    } else {
        let quotient = dividend_num / divisor_num;
        let remainder = dividend_num % divisor_num;
        (nat_to_bits(quotient), nat_to_bits(remainder))
    }
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
/* code modified by LLM (iteration 4): fixed unsupported iter().rev() by using while loop */ {
    fn compute_str_to_nat(s: &[char]) -> u128 {
        let mut res: u128 = 0;
        let mut pos = s.len();
        while pos > 0 {
            pos -= 1;
            res = (res << 1) | if s[pos] == '1' { 1 } else { 0 };
        }
        res
    }
    fn nat_to_bits(nn: u128) -> Vec<char> {
        if nn == 0 {
            return vec!['0'];
        }
        let mut res = Vec::new();
        let mut n = nn;
        while n > 0 {
            res.push(if n % 2 == 0 { '0' } else { '1' });
            n = n >> 1;
        }
        res.reverse();
        res
    }
    fn mod_exp_recursive(base: u128, exp: u128, mod_: u128) -> u128 {
        if exp == 0 {
            1
        } else if exp % 2 == 0 {
            let half = mod_exp_recursive(base, exp / 2, mod_);
            ((half as u128 * half as u128) % mod_) as u128
        } else {
            let rest = mod_exp_recursive(base, exp - 1, mod_);
            ((base as u128 * rest as u128) % mod_) as u128
        }
    }
    let x = compute_str_to_nat(sx);
    let e = compute_str_to_nat(sy);
    let m = compute_str_to_nat(sz);
    if m <= 1 {
        vec!['0']
    } else {
        let result = mod_exp_recursive(x, e, m);
        nat_to_bits(result)
    }
}
// </vc-code>

fn main() {}
}


