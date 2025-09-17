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
    let mut result_vec = Vec::<char>::new();
    if sum == 0 {
        result_vec.push('0');
        return result_vec;
    }
    let mut current_sum = sum;
    while current_sum > 0
        invariant
            result_vec@.len() >= 0,
            ValidBitString(result_vec@),
            sum == Str2Int(result_vec@) + current_sum * Exp_int(2, result_vec@.len() as nat),
            current_sum >= 0
        decreases current_sum
    {
        if current_sum % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_sum = current_sum / 2;
    }
    result_vec.reverse();
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
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;
    let mut result_vec = Vec::<char>::new();
    if product == 0 {
        result_vec.push('0');
        return result_vec;
    }
    let mut current_product = product;
    while current_product > 0
        invariant
            result_vec@.len() >= 0,
            ValidBitString(result_vec@),
            product == Str2Int(result_vec@) + current_product * Exp_int(2, result_vec@.len() as nat),
            current_product >= 0
        decreases current_product
    {
        if current_product % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_product = current_product / 2;
    }
    result_vec.reverse();
    result_vec
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

    let mut result = 1nat;
    let mut base = x % z;
    let mut exponent = y;

    while exponent > 0
        invariant
            exponent >= 0,
            result * Exp_int(base, exponent) % z == Exp_int(x, y) % z,
            z > 1
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exponent = exponent / 2;
    }

    let mut result_vec = Vec::<char>::new();
    if result == 0 {
        result_vec.push('0');
        return result_vec;
    }
    let mut current_result = result;
    while current_result > 0
        invariant
            result_vec@.len() >= 0,
            ValidBitString(result_vec@),
            result == Str2Int(result_vec@) + current_result * Exp_int(2, result_vec@.len() as nat),
            current_result >= 0
        decreases current_result
    {
        if current_result % 2 == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_result = current_result / 2;
    }
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}


