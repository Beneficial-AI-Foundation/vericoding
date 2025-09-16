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
    let mut res = Vec::<char>::new();
    let len1 = s1.len();
    let len2 = s2.len();
    let mut carry = 0i32;
    let mut i = 0usize;
    let max_len = if len1 > len2 { len1 } else { len2 };
    while i < max_len || carry != 0 {
        let b1 = if i < len1 { (if s1[i] == '1' { 1 } else { 0 }) } else { 0i32 };
        let b2 = if i < len2 { (if s2[i] == '1' { 1 } else { 0 }) } else { 0i32 };
        let sum = b1 + b2 + carry;
        carry = sum / 2;
        let bit = sum % 2;
        res.push(if bit == 1 { '1' } else { '0' });
        i += 1;
    }
    res
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let len1 = s1.len() as usize;
    let len2 = s2.len() as usize;
    let mut res = vec!['0'; len1 + len2];
    for j in 0..len2 {
        if s2[j] == '1' {
            let mut carry = 0i32;
            let mut k = j;
            let mut i = 0;
            while i < len1 || carry != 0 {
                let b1 = if i < len1 { if s1[i] == '1' { 1 } else { 0 } } else { 0i32 };
                let current = if k < res.len() { if res[k] == '1' { 1 } else { 0 } } else { 0i32 };
                let sum = b1 + current + carry;
                carry = sum / 2;
                res[k] = if sum % 2 == 1 { '1' } else { '0' };
                k += 1;
                i += 1;
            }
        }
    }
    if res.is_empty() { res.push('0'); }
    res
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
    let mut result = s1@;
    if sy@.len() == 0 || (sy@.len() == 1usize && sy@[0] == '0') {
        vec!['1']
    } else {
        let mut exponent = n;
        while exponent > 0 {
            result = Mul(&result, &result).as_slice();
            exponent = exponent - 1;
        }
        return Mul(&result, vec!['0'].as_slice());
    }
}
// </vc-code>

fn main() {}
}
