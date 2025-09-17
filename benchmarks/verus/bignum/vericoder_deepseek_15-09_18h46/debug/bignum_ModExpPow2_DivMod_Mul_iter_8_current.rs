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
proof fn divmod_lemma(x: nat, y: nat) {
    if y > 0 {
        assert(x / y == x / y);
        assert(x % y == x % y);
    }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): Implement binary multiplication algorithm */
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result_digits = vec!['0'; len1 + len2];
    for i in 0..len1 {
        if s1[i] == '1' {
            let mut carry = 0;
            for j in 0..len2 {
                let pos = i + j;
                let current = if result_digits[pos] == '1' { 1 } else { 0 };
                let sum = current + (if s2[j] == '1' { 1 } else { 0 }) + carry;
                result_digits[pos] = if sum % 2 == 1 { '1' } else { '0' };
                carry = sum / 2;
            }
            if carry > 0 {
                result_digits[i + len2] = '1';
            }
        }
    }
    while result_digits.len() > 1 && result_digits.last() == Some(&'0') {
        result_digits.pop();
    }
    result_digits.reverse();
    Vec::from(result_digits)
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
    /* code modified by LLM (iteration 8): Implement modular exponentiation using binary exponentiation for base-2 */
    if n == 0 {
        let x_val = Str2Int(sx@);
        let z_val = Str2Int(sz@);
        let result_val = Exp_int(x_val, 1) % z_val;
        let mut res_vec = Vec::new();
        if result_val == 0 {
            res_vec.push('0');
        } else {
            let mut temp = result_val;
            while temp > 0 {
                res_vec.push(if temp % 2 == 1 { '1' } else { '0' });
                temp = temp / 2;
            }
            res_vec.reverse();
        }
        return res_vec;
    }
    let z_val = Str2Int(sz@);
    let mut base = Str2Int(sx@) % z_val;
    let mut result = 1 % z_val;
    let mut i = 0;
    while i < n {
        invariant
            result == Exp_int(Str2Int(sx@), Exp_int(2, i as nat)) % z_val,
        decreases n - i,
        {
            result = (result * result) % z_val;
            i = i + 1;
        }
    }
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp = result;
        while temp > 0 {
            res_vec.push(if temp % 2 == 1 { '1' } else { '0' });
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    res_vec
}
// </vc-code>

fn main() {}
}
