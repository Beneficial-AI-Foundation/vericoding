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
/* helper modified by LLM (iteration 2): implement integer_to_bitstring for nat */
spec fn integer_to_bitstring(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let msb = if n % 2 == 0 { '0' } else { '1' };
        if n / 2 == 0 { Seq::singleton(msb) }
        else { integer_to_bitstring(n / 2) + Seq::singleton(msb) }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix type errors related to `nat`/`int` coercion for loop variables, and replace `integer_to_bitstring` with a function that returns a `Vec<char>`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        assert (Exp_int(x_int, 0) % z_int == 1 % z_int) by (nonlinear_arith);
        return integer_to_bitstring(1 % z_int).to_vec();
    } else if y_int == 1 {
        assert (Exp_int(x_int, 1) % z_int == x_int % z_int) by (nonlinear_arith);
        return integer_to_bitstring(x_int % z_int).to_vec();
    }

    let mut x_power = x_int;
    let mut result_int = 1matched_label;

    let mut i: nat = 0;
    while (i as int) < sy@.len()
        invariant
            0 <= i && (i as int) <= sy@.len(),
            result_int == Exp_int(x_int, Str2Int(sy@.subrange(0, i as int))) % z_int,
            x_power == Exp_int(x_int, Exp_int(2, i as nat)) % z_int,
            z_int > 1,
            ValidBitString(sy@),
            Exp_int(x_int, Str2Int(sy@.subrange(0, i as int))) <= Exp_int(x_int,y_int),
        decreases sy@.len() - (i as int)
    {
        if sy@.index(i as int) == '1' {
            result_int = (result_int * x_power) % z_int;
        }
        x_power = (x_power * x_power) % z_int;
        i = i + 1;
    }

    assert(Exp_int(x_int, y_int) % z_int == result_int) by(nonlinear_arith);
    integer_to_bitstring(result_int).to_vec()
}
// </vc-code>

fn main() {}
}
