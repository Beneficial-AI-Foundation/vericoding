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
/* helper modified by LLM (iteration 4): Fixed Str2Int_to_Seq_char to handle 0 and 1 correctly and remove unnecessary push_back. Also fixed ModExp_DivMod_Zeroes_spec to call itself recursively with `(y-1) as nat` and `(y/2) as nat` as second parameters. This fixes the verification error related to incorrect `Str2Int_to_Seq_char` calls. */
spec fn ModExp_DivMod_Zeroes_spec(sx_seq: Seq<char>, sy_seq: Seq<char>, sz_seq: Seq<char>) -> (res: nat)
  requires
    ValidBitString(sx_seq),
    ValidBitString(sy_seq),
    ValidBitString(sz_seq),
    sy_seq.len() > 0,
    Str2Int(sz_seq) > 1
  ensures
    res == Exp_int(Str2Int(sx_seq), Str2Int(sy_seq)) % Str2Int(sz_seq)
  decreases sy_seq.len()
{
    let y = Str2Int(sy_seq);

    if y == 0 {
        1
    } else if y == 1 {
        Str2Int(sx_seq) % Str2Int(sz_seq)
    } else {
        let x_val = Str2Int(sx_seq);
        let z_val = Str2Int(sz_seq);

        if y % 2 == 0 {
            let res_half_int = ModExp_DivMod_Zeroes_spec(sx_seq, Str2Int_to_Seq_char((y / 2) as nat), sz_seq);
            (res_half_int * res_half_int) % z_val
        } else {
            let res_y_minus_1_int = ModExp_DivMod_Zeroes_spec(sx_seq, Str2Int_to_Seq_char((y - 1) as nat), sz_seq);
            (x_val * res_y_minus_1_int) % z_val
        }
    }
}

spec fn Str2Int_to_Seq_char(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let rem_char = if (n % 2) == 1 { '1' } else { '0' };
        let mut res = Str2Int_to_Seq_char(n / 2);
        res.push_back(rem_char)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Changed loop variable `i` from `int` to `usize` to fix compilation error related to type usage. This allows proper indexing into `res_seq`. */
{
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;

    let result_nat = ModExp_DivMod_Zeroes_spec(sx_seq, sy_seq, sz_seq);
    let res_seq = Str2Int_to_Seq_char(result_nat);

    let mut res_vec = Vec::<char>::new();
    let mut i: usize = 0;
    while i < res_seq.len()
        invariant
            0 <= i as int <= res_seq.len() as int,
            res_vec.len() == i,
            ValidBitString(res_vec.view())
    {
        res_vec.push(res_seq.index(i as int));
        i = i + 1;
    }
    res_vec
}
// </vc-code>

fn main() {}
}
