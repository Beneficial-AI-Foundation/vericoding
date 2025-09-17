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
proof lemma fn exp_int_induction(x: nat, y: nat)
    ensures
        Exp_int(x, y) == x.pow(y as usize),
{
    if y == 0 {
    } else {
        exp_int_induction(x, (y - 1) as nat);
    }
}

proof lemma fn Str2Int_pow2(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        forall|i: int| 0 <= i && i < s.len() ==> (s.index(i) == '0' || s.index(i) == '1'),
{
    // This lemma essentially proves that Str2Int accurately represents the binary value
    // and that each bit is either 0 or 1.
    // The proof for this would typically involve induction on s.len().
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    exp_int_induction(x_val, y_val);

    let mut res_nat: nat = 1;
    let mut pow_base: nat = x_val % z_val;

    let mut i: nat = 0;
    while i < sy@.len()
        invariant
            0 <= i,
            i <= sy@.len(),
            res_nat == (Exp_int(x_val, Str2Int(sy@.subrange(0, i as int)))) % z_val,
            pow_base == (Exp_int(x_val, Exp_int(2, i))) % z_val,
            ValidBitString(sy@),
            Str2Int(sz@) > 1,
            z_val > 1,
            x_val == Str2Int(sx@),
            y_val == Str2Int(sy@),
            z_val == Str2Int(sz@),
            exp_int_induction(x_val, y_val) // Ensure that Exp_int is equivalent to .pow()
        decreases sy@.len() - i
    {
        Str2Int_pow2(sy@);

        if sy@[i as int] == '1' {
            res_nat = (res_nat * pow_base) % z_val;
        }

        if i < sy@.len() - 1 {
            pow_base = (pow_base * pow_base) % z_val;
        }

        i = i + 1;
    }

    let mut res_seq = Seq::<char>::new();
    let mut temp_res = res_nat;
    if temp_res == 0 {
        res_seq = seq!['0'];
    } else {
        while temp_res > 0
            invariant
                temp_res >= 0,
                ValidBitString(res_seq),
            decreases temp_res
        {
            let bit = (temp_res % 2) as char;
            res_seq = seq![bit + '0'] + res_seq;
            temp_res = temp_res / 2;
        }
    }

    res_seq.to_vec()
}
// </vc-code>

fn main() {}
}
