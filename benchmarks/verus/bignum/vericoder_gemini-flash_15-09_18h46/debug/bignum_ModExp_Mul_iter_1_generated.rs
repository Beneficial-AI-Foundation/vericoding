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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;

    let mut bit_string: Vec<char> = Vec::new();
    if product == 0 {
        bit_string.push('0');
        return bit_string;
    }

    let mut temp = product;
    while temp > 0
        invariant
            bit_string.len() <= product.height() + 1,
            temp >= 0,
            temp as int >= 0,
            forall |i: int| 0 <= i && i < bit_string.len() ==> (bit_string.index(i) == '0' || bit_string.index(i) == '1'),
            Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == product
        decreases temp
    {
        if temp % 2 == 1 {
            bit_string.push('1');
        } else {
            bit_string.push('0');
        }
        temp = temp / 2;
    }
    bit_string.reverse();
    bit_string
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

    if y == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }

    let mut result_vec = ModExp(sx, sy.subslice(0, sy.len() - 1), sz);
    let mut result_nat = Str2Int(result_vec@);

    if sy.last()@[0] == '1' {
        result_nat = (result_nat * x) % z;
    }

    result_nat = (result_nat * result_nat) % z;

    let mut bit_string: Vec<char> = Vec::new();
    if result_nat == 0 {
        bit_string.push('0');
        return bit_string;
    }

    let mut temp = result_nat;
    while temp > 0
        invariant
            bit_string.len() <= result_nat.height() + 1,
            temp >= 0,
            temp as int >= 0,
            forall |i: int| 0 <= i && i < bit_string.len() ==> (bit_string.index(i) == '0' || bit_string.index(i) == '1'),
            Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == result_nat
        decreases temp
    {
        if temp % 2 == 1 {
            bit_string.push('1');
        } else {
            bit_string.push('0');
        }
        temp = temp / 2;
    }
    bit_string.reverse();
    bit_string
}
// </vc-code>

fn main() {}
}
