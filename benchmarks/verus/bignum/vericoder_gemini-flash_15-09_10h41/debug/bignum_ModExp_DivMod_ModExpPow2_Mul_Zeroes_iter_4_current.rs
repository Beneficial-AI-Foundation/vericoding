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
/* helper modified by LLM (iteration 4): ensure integer_to_bitstring handles `n=0` by returning a `Seq<char>` and fixes recursion for `n/2` being 0 rather than `n` itself */
spec fn integer_to_bitstring(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let msb = if n % 2 == 0 { '0' } else { '1' };
        if n / 2 == 0 && n % 2 == 1 { Seq::singleton(msb) }
        else if n / 2 == 0 && n % 2 == 0 {
            // This case should ideally not happen for n>0 if `msb` is based on n%2 earlier
            // but to be safe, we'll handle it by just returning '0' (for n=0, though it's covered by the first branch)
            // For n>0 and n/2==0, n must be 1, in which case msb is '1' and it's covered by the previous clause. So this branch is dead.
            Seq::singleton('0')
        }
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
/* code modified by LLM (iteration 4): Changed type of `i` to `int` to allow direct use in comparisons and indexing without casting, resolving compilation errors. */
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
    let mut result_int = 1nat;

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
    integer_to_bitstring(result_int).to_vec()
}
// </vc-code>

fn main() {}
}
