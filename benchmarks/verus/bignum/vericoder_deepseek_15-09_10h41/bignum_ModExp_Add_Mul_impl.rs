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
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let sum = n1 + n2;
    let mut num = sum as int;
    let mut result = Vec::new();
    while num > 0
        invariant
            num >= 0,
            ValidBitString(result@),
            sum as int == num * Exp_int(2, result.len() as nat) + Str2Int(result@),
    {
        if num % 2 == 1 {
            result.push('1');
            num = (num - 1) / 2;
        } else {
            result.push('0');
            num = num / 2;
        }
    }
    result.reverse();
    if result.is_empty() {
        result.push('0');
    }
    result
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;
    let mut num = product as int;
    let mut result = Vec::new();
    while num > 0
        invariant
            num >= 0,
            ValidBitString(result@),
            product as int == num * Exp_int(2, result.len() as nat) + Str2Int(result@),
    {
        if num % 2 == 1 {
            result.push('1');
            num = (num - 1) / 2;
        } else {
            result.push('0');
            num = num / 2;
        }
    }
    result.reverse();
    if result.is_empty() {
        result.push('0');
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
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    let exp = Exp_int(x, y);
    let remainder = exp % z;
    let mut num = remainder as int;
    let mut result = Vec::new();
    while num > 0
        invariant
            num >= 0,
            ValidBitString(result@),
            remainder as int == num * Exp_int(2, result.len() as nat) + Str2Int(result@),
    {
        if num % 2 == 1 {
            result.push('1');
            num = (num - 1) / 2;
        } else {
            result.push('0');
            num = num / 2;
        }
    }
    result.reverse();
    if result.is_empty() {
        result.push('0');
    }
    result
}
// </vc-code>

fn main() {}
}


