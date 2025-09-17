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
/* helper modified by LLM (iteration 5): Corrected `Seq::singleton` to `Seq::new` and `Seq::push` for character sequences. */
spec fn ModExpAux(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let res = ModExpAux(x, y / 2, z);
        (res * res) % z
    } else {
        let res = ModExpAux(x, (y - 1) as nat / 2, z);
        (x * res * res) % z
    }
}

spec fn ModExp(x: nat, y: nat, z: nat) -> nat
{
    if z == 0 { 0 } else { ModExpAux(x % z, y, z) }
}

spec fn NatToBitString(n: nat) -> (s: Seq<char>)
decreases n
{
    if n == 0 { Seq::new().push('0') }
    else {
        let rem = n % 2;
        let div = n / 2;
        if div == 0 { Seq::new().push(if rem == 1 { '1' } else { '0' }) }
        else { Seq::new().push(if rem == 1 { '1' } else { '0' }).add(NatToBitString(div)) }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `bit_string_seq.to_vec()` with `bit_string_seq.into_vec()` to resolve a compilation error */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);
    let result_nat = ModExp(x_int, y_int, z_int);
    let bit_string_seq = NatToBitString(result_nat);
    bit_string_seq.into_vec()
}
// </vc-code>

fn main() {}
}
