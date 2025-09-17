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
/* code modified by LLM (iteration 2): fixed int to usize for indices and adjusted invariant */
{
            let mut result = Vec::<char>::new();
            let mut i = s1.len();   // usize
            let mut j = s2.len();   // usize
            let mut carry = false;

            while i > 0 || j > 0 || carry
                invariant
                    0 <= i as int <= s1.len() as int,
                    0 <= j as int <= s2.len() as int,
                    ValidBitString(s1@.subrange(i as int, s1.len() as int)),
                    ValidBitString(s2@.subrange(j as int, s2.len() as int)),
                    ValidBitString(result@.rev()),
                decreases (i as int + j as int)
            {
                let digit1 = if i > 0 { s1[i - 1] } else { '0' };
                let digit2 = if j > 0 { s2[j - 1] } else { '0' };

                let (sum, new_carry) = match (digit1, digit2, carry) {
                    ('1', '1', true) => ('1', true),
                    ('1', '1', false) => ('0', true),
                    ('1', '0', true) => ('0', true),
                    ('1', '0', false) => ('1', false),
                    ('0', '1', true) => ('0', true),
                    ('0', '1', false) => ('1', false),
                    ('0', '0', true) => ('1', false),
                    ('0', '0', false) => ('0', false),
                    (_, _, _) => panic!("Invalid binary digit"),
                };

                result.push(sum);
                carry = new_carry;

                if i > 0 { i -= 1; }
                if j > 0 { j -= 1; }
            }

            result.reverse();
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
/* code modified by LLM (iteration 2): replaced ghost conversions with u64 helpers */
{
            // Helper function to convert binary string to u64
            fn binary_to_u64(s: &[char]) -> u64 {
                let mut res = 0;
                for c in s {
                    res = res * 2 + if *c == '1' { 1 } else { 0 };
                }
                res
            }

            // Helper function to convert u64 to binary string
            fn u64_to_binary(n: u64) -> Vec<char> {
                if n == 0 {
                    return vec!['0'];
                }
                let mut res = Vec::new();
                let mut num = n;
                while num > 0 {
                    res.push(if num % 2 == 1 { '1' } else { '0' });
                    num = num / 2;
                }
                res.reverse();
                res
            }

            let dividend_int = binary_to_u64(dividend);
            let divisor_int = binary_to_u64(divisor);

            let quotient_int = dividend_int / divisor_int;
            let remainder_int = dividend_int % divisor_int;

            let quotient = u64_to_binary(quotient_int);
            let remainder = u64_to_binary(remainder_int);

            (quotient, remainder)
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
/* code modified by LLM (iteration 2): replaced ghost conversions with u64 helpers */
{
            // Helper function to convert binary string to u64
            fn binary_to_u64(s: &[char]) -> u64 {
                let mut res = 0;
                for c in s {
                    res = res * 2 + if *c == '1' { 1 } else { 0 };
                }
                res
            }

            // Helper function to convert u64 to binary string
            fn u64_to_binary(n: u64) -> Vec<char> {
                if n == 0 {
                    return vec!['0'];
                }
                let mut res = Vec::new();
                let mut num = n;
                while num > 0 {
                    res.push(if num % 2 == 1 { '1' } else { '0' });
                    num = num / 2;
                }
                res.reverse();
                res
            }

            let x = binary_to_u64(sx);
            let y = binary_to_u64(sy);
            let z = binary_to_u64(sz);

            let mut result = 1 % z;
            let mut base = x % z;
            let mut exp = y;

            while exp > 0 {
                if exp % 2 == 1 {
                    result = (result * base) % z;
                }
                base = (base * base) % z;
                exp = exp / 2;
            }

            u64_to_binary(result)
        }
// </vc-code>

fn main() {}
}


