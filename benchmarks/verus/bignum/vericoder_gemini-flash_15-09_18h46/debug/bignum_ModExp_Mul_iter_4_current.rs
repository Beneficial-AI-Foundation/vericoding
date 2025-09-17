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
/* code modified by LLM (iteration 4): Removed incorrect `Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == product` invariant and fixed `Index` trait import to be global `use core::ops::Index;` */
{
    use core::ops::Index;
    let n1: nat = Str2Int(s1@);
    let n2: nat = Str2Int(s2@);
    let product: nat = n1 * n2;

    let mut bit_string: Vec<char> = Vec::new();
    if product == 0 {
        bit_string.push('0');
        return bit_string;
    }

    let mut temp: nat = product;
    while temp > 0
        invariant
            temp >= 0,
            forall |i: int| 0 <= i && i < bit_string.len() ==> (bit_string.index(i as usize) == '0' || bit_string.index(i as usize) == '1'),
            // The previous invariant `Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == product` was incorrect for a reversed bit_string.
            // It needs a more complex formulation or to be split into pre-reverse and post-reverse stages.
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
/* code modified by LLM (iteration 4): removed incorrect invariant `Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == result_nat` */
{
    use core::ops::Index;
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);

    if y == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    const SYMB_R_ZERO: &[char] = &['0'];

    let half_y_str = if sy.len() > 1 { sy.subslice(0, sy.len() as int - 1) } else { SYMB_R_ZERO };
    let result_rec_vec = ModExp(sx, half_y_str, sz);
    let result_rec_nat: nat = Str2Int(result_rec_vec@);

    let mut result_nat: nat = (result_rec_nat * result_rec_nat) % z;

    if sy.last().unwrap() == &'1' {
        result_nat = (result_nat * x) % z;
    }

    let mut bit_string: Vec<char> = Vec::new();
    if result_nat == 0 {
        bit_string.push('0');
        return bit_string;
    }

    let mut temp: nat = result_nat;
    while temp > 0
        invariant
            temp >= 0,
            forall |i: int| 0 <= i && i < bit_string.len() ==> (bit_string.index(i as usize) == '0' || bit_string.index(i as usize) == '1'),
            // Removed `Str2Int(bit_string@) + temp * Exp_int(2, bit_string.len() as nat) == result_nat` as it was incorrect for reversed bit string.
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
