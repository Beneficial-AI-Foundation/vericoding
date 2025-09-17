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
/* helper modified by LLM (iteration 3): Removed Str2Seq calls from spec function and directly returns 'nat' type. Also fixed the `y-1` to `(y-1) as nat` */
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
            let half_y_seq = Str2Int_to_Seq_char((y / 2) as nat);
            let res_half_int = ModExp_DivMod_Zeroes_spec(sx_seq, half_y_seq, sz_seq);
            (res_half_int * res_half_int) % z_val
        } else {
            let y_minus_1_seq = Str2Int_to_Seq_char((y - 1) as nat);
            let res_y_minus_1_int = ModExp_DivMod_Zeroes_spec(sx_seq, y_minus_1_seq, sz_seq);
            (x_val * res_y_minus_1_int) % z_val
        }
    }
}

spec fn Str2Int_to_Seq_char(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
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
/* code modified by LLM (iteration 3): Fixed compilation error related to invalid type usage of 'int' and 'nat'.
Added helper fn Str2Int_to_Seq_char for converting from nat to Seq<char>.
Call ModExp_DivMod_Zeroes_spec to get a nat, and then convert it to Seq<char> using the helper before creating the Vec<char>.
*/
{
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;

    let result_nat = ModExp_DivMod_Zeroes_spec(sx_seq, sy_seq, sz_seq);
    let res_seq = Str2Int_to_Seq_char(result_nat);

    let mut res_vec = Vec::<char>::new();
    let mut i: int = 0;
    while i < res_seq.len() as int
        invariant
            0 <= i <= res_seq.len() as int,
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
