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
spec fn SeqToVec(s: Seq<char>) -> Vec<char> {
    let mut v: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s.len() {
        v.push(s.index(i));
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if Str2Int(sy@) == 0 {
        let mut vec = Vec::<char>::new();
        vec.push('1');
        return vec;
    }
    let mut sx_vec = sx.to_vec();
    let mut sy_vec = sy.to_vec();
    let mut sz_vec = sz.to_vec();

    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        let mut vec_result = Vec::<char>::new();
        vec_result.push('1');
        return vec_result;
    }

    let mut result_x: nat = x;
    let mut result_y: nat = y;
    let mut res_nat: nat = 1;

    while result_y > 0
        invariant
            result_x == Str2Int(sx@).nat_mod(Str2Int(sz@)),
            res_nat * (result_x.pow(result_y)).nat_mod(z) == (x.pow(y)).nat_mod(z),
            Str2Int(sz@) > 1
        decreases result_y
    {
        if result_y % 2 == 1 {
            res_nat = (res_nat * result_x).nat_mod(z);
        }
        result_x = (result_x * result_x).nat_mod(z);
        result_y = result_y / 2;
    }

    // Convert res_nat back to a bit string (Vec<char>)
    let mut res_vec = Vec::<char>::new();
    if res_nat == 0 {
        res_vec.push('0');
    } else {
        let mut temp_nat = res_nat;
        while temp_nat > 0
            invariant
                temp_nat >= 0
            decreases temp_nat
        {
            if temp_nat % 2 == 1 {
                res_vec.push('1');
            } else {
                res_vec.push('0');
            }
            temp_nat = temp_nat / 2;
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

fn main() {}
}
