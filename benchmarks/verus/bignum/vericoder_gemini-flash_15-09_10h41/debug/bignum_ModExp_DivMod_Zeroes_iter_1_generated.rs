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
spec fn ModExp_DivMod_Zeroes_spec(sx_seq: Seq<char>, sy_seq: Seq<char>, sz_seq: Seq<char>) -> (res: Seq<char>)
  requires
    ValidBitString(sx_seq),
    ValidBitString(sy_seq),
    ValidBitString(sz_seq),
    sy_seq.len() > 0,
    Str2Int(sz_seq) > 1
  ensures
    ValidBitString(res),
    Str2Int(res) == Exp_int(Str2Int(sx_seq), Str2Int(sy_seq)) % Str2Int(sz_seq)
  decreases sy_seq.len()
{
    if sy_seq.len() == 1 {
        let y0 = sy_seq.index(0);
        if y0 == '0' {
            return Str2Seq(1);
        }
    }

    let y = Str2Int(sy_seq);

    if y == 0 {
        return Str2Seq(1);
    } else if y == 1 {
        return Str2Seq(Str2Int(sx_seq) % Str2Int(sz_seq));
    }

    let x_val = Str2Int(sx_seq);
    let z_val = Str2Int(sz_seq);

    if y % 2 == 0 {
        let half_y_seq = Str2Seq(y / 2);
        let res_half = ModExp_DivMod_Zeroes_spec(sx_seq, half_y_seq, sz_seq);
        let res_half_int = Str2Int(res_half);
        return Str2Seq((res_half_int * res_half_int) % z_val);
    } else {
        let y_minus_1_seq = Str2Seq(y - 1);
        let res_y_minus_1 = ModExp_DivMod_Zeroes_spec(sx_seq, y_minus_1_seq, sz_seq);
        let res_y_minus_1_int = Str2Int(res_y_minus_1);
        return Str2Seq((x_val * res_y_minus_1_int) % z_val);
    }
}

spec fn Str2Seq(n: nat) -> Seq<char>
  ensures ValidBitString(Str2Seq(n))
  decreases n
{
    if n == 0 {
        return (Seq::<char>::empty()).push('0');
    }
    let mut result = Seq::<char>::empty();
    let mut num = n;
    while num > 0
        invariant
            ValidBitString(result),
            num >= 0
    {
        if num % 2 == 1 {
            result = (Seq::<char>::empty()).push('1').add(result);
        } else {
            result = (Seq::<char>::empty()).push('0').add(result);
        }
        num = num / 2;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;

    let res_seq = ModExp_DivMod_Zeroes_spec(sx_seq, sy_seq, sz_seq);

    let mut res_vec = Vec::<char>::new();
    let mut i = 0;
    while i < res_seq.len()
        invariant
            0 <= i <= res_seq.len(),
            res_vec.len() == i,
            ValidBitString(res_vec.view())
    {
        res_vec.push(res_seq.index(i));
        i = i + 1;
    }
    res_vec
}
// </vc-code>

fn main() {}
}
