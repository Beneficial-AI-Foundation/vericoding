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

// <vc-helpers>
spec fn Str2Int_to_int_auto_convert(s: Seq<char>) -> int
recommends ValidBitString(s)
{
    Str2Int(s) as int
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        let mut vec = Vec::new();
        vec.push('1');
        return vec;
    }

    let half_y = y / 2;
    let mut res_half = ModExp_DivMod_ModExpPow2(sx, &sy.subslice(0, half_y as int), sz);
    let res_half_int = Str2Int(res_half@);

    let mut res_full_int = (res_half_int * res_half_int) % z;

    if y % 2 == 1 {
        res_full_int = (res_full_int * x) % z;
    }

    let mut res_vec = Vec::new();
    let mut temp = res_full_int;
    if temp == 0 {
        res_vec.push('0');
        return res_vec;
    }

    while temp > 0 {
        if temp % 2 == 1 {
            res_vec.insert(0, '1');
        } else {
            res_vec.insert(0, '0');
        }
        temp = temp / 2;
    }

    res_vec
}
// </vc-code>

fn main() {}
}
