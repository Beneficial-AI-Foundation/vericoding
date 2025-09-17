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
/* code modified by LLM (iteration 4): fixed type mismatches by using proper Verus literals */
{
    let dividend_int = Str2Int(dividend@);
    let divisor_int = Str2Int(divisor@);
    let quotient_int = dividend_int / divisor_int;
    let remainder_int = dividend_int % divisor_int;

    // Convert quotient_int to bit string
    let quotient_bits = if quotient_int == 0nat {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut temp = quotient_int;
        let mut value = 0nat;
        let mut power = 1nat;
        while temp > 0nat
            invariant
                temp >= 0nat,
                quotient_int == temp * power + value,
                power == 1nat << (bits.len() as nat),
            decreases temp
        {
            let bit = if temp % 2nat == 1nat { '1' } else { '0' };
            bits.push(bit);
            if bit == '1' {
                value += power;
            }
            power *= 2nat;
            temp = temp / 2nat;
        }
        bits.reverse();
        bits
    };

    // Convert remainder_int to bit string
    let remainder_bits = if remainder_int == 0nat {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut temp = remainder_int;
        let mut value = 0nat;
        let mut power = 1nat;
        while temp > 0nat
            invariant
                temp >= 0nat,
                remainder_int == temp * power + value,
                power == 1nat << (bits.len() as nat),
            decreases temp
        {
            let bit = if temp % 2nat == 1nat { '1' } else { '0' };
            bits.push(bit);
            if bit == '1' {
                value += power;
            }
            power *= 2nat;
            temp = temp / 2nat;
        }
        bits.reverse();
        bits
    };

    return (quotient_bits, remainder_bits);
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
/* code modified by LLM (iteration 4): fixed type mismatches by using proper Verus literals */
{
    if n == 0int {
        if Str2Int(sy@) == 0nat {
            let result_int = 1nat % Str2Int(sz@);
            let result_bits = if result_int == 0nat {
                vec!['0']
            } else {
                let mut bits = Vec::new();
                let mut temp = result_int;
                let mut value = 0nat;
                let mut power = 1nat;
                while temp > 0nat
                    invariant
                        temp >= 0nat,
                        result_int == temp * power + value,
                        power == 1nat << (bits.len() as nat),
                    decreases temp
                {
                    let bit = if temp % 2nat == 1nat { '1' } else { '0' };
                    bits.push(bit);
                    if bit == '1' {
                        value += power;
                    }
                    power *= 2nat;
                    temp = temp / 2nat;
                }
                bits.reverse();
                bits
            };
            return result_bits;
        } else {
            let result_int = Str2Int(sx@) % Str2Int(sz@);
            let result_bits = if result_int == 0nat {
                vec!['0']
            } else {
                let mut bits = Vec::new();
                let mut temp = result_int;
                let mut value = 0nat;
                let mut power = 1nat;
                while temp > 0nat
                    invariant
                        temp >= 0nat,
                        result_int == temp * power + value,
                        power == 1nat << (bits.len() as nat),
                    decreases temp
                {
                    let bit = if temp % 2nat == 1nat { '1' } else { '0' };
                    bits.push(bit);
                    if bit == '1' {
                        value += power;
                    }
                    power *= 2nat;
                    temp = temp / 2nat;
                }
                bits.reverse();
                bits
            };
            return result_bits;
        }
    } else {
        let mut new_sy = Vec::new();
        new_sy.push('1');
        let mut i = 1int;
        while i < n {
            new_sy.push('0');
            i += 1int;
        }
        let temp = ModExpPow2(sx, &new_sy, n - 1int, sz);
        let temp_int = Str2Int(temp@);
        let result_int = (temp_int * temp_int) % Str2Int(sz@);
        let result_bits = if result_int == 0nat {
            vec!['0']
        } else {
            let mut bits = Vec::new();
            let mut temp = result_int;
            let mut value = 0nat;
            let mut power = 1nat;
            while temp > 0nat
                invariant
                    temp >= 0nat,
                    result_int == temp * power + value,
                    power == 1nat << (bits.len() as nat),
                decreases temp
            {
                let bit = if temp % 2nat == 1nat { '1' } else { '0' };
                bits.push(bit);
                if bit == '1' {
                    value += power;
                }
                power *= 2nat;
                temp = temp / 2nat;
            }
            bits.reverse();
            bits
        };
        return result_bits;
    }
}
// </vc-code>

fn main() {}
}


