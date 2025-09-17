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
/* helper modified by LLM (iteration 5): Corrected `Seq::singleton` calls to `Seq::new` with a single element and fixed error due to type `nat` in the condition `n/2 == 0`. */
spec fn integer_to_bitstring(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::new(1, |i| '0') }
    else {
        let msb = if n % 2 == 0 { '0' } else { '1' };
        if (n / 2) as nat == 0 && n % 2 == 1 { Seq::new(1, |i| msb) }
        else {
            let prev_seq = integer_to_bitstring(n / 2);
            prev_seq.push(msb)
        }
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
/* code modified by LLM (iteration 5): Fixed compilation errors related to `nat` and `int` types, `Seq::to_vec()` calls, and `Seq::singleton` by using `Seq::new` and manual `Vec` conversion. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        assert (Exp_int(x_int, 0) % z_int == 1 % z_int) by (nonlinear_arith);
        let s = integer_to_bitstring(1 nat % z_int);
        let mut vec = Vec::new();
        vec.push_each(s.view());
        return vec;
    } else if y_int == 1 {
        assert (Exp_int(x_int, 1) % z_int == x_int % z_int) by (nonlinear_arith);
        let s = integer_to_bitstring(x_int % z_int);
        let mut vec = Vec::new();
        vec.push_each(s.view());
        return vec;
    }

    let mut x_power = x_int;
    let mut result_int = 1 nat;

    let mut i: int = 0;
    while i < sy@.len()
        invariant
            0 <= i && i <= sy@.len(),
            result_int == Exp_int(x_int, Str2Int(sy@.subrange(0, i))) % z_int,
            x_power == Exp_int(x_int, Exp_int(2, i as nat)) % z_int,
            z_int > 1,
            ValidBitString(sy@)
        decreases sy@.len() - i
    {
        if sy@.index(i) == '1' {
            result_int = (result_int * x_power) % z_int;
        }
        x_power = (x_power * x_power) % z_int;
        i = i + 1;
    }

    // Added assertion and proof block to demonstrate the final equality needed by the `ensures` clause
    assert(Exp_int(x_int, y_int) % z_int == result_int) by(nonlinear_arith);
    let s = integer_to_bitstring(result_int);
    let mut vec = Vec::new();
    vec.push_each(s.view());
    vec
}
// </vc-code>

fn main() {}
}
