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
/* helper modified by LLM (iteration 5): changed Int2Str ensures to use && for compilation */
spec fn ModExp(x: nat, y: nat, m: nat) -> nat
    requires
        m > 1,
    ensures
        ModExp(x, y, m) == Exp_int(x, y) % m,
    decreases y
{
    if y == 0 {
        1
    } else if y % 2 == 0 {
        let half = ModExp(x, (y / 2) as nat, m);
        (half * half) % m
    } else {
        let rest = ModExp(x, ((y - 1) as nat), m);
        (x * rest) % m
    }
}

spec fn Int2Str(n: nat) -> Seq<char>
    ensures ValidBitString(result) && Str2Int(result) == n,
    decreases n
{
    if n == 0 { Seq::empty() } else {
        let rest = Int2Str((n / 2) as nat);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        rest.push(bit)
    }
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
    let ghost x = Str2Int(sx@);
    let ghost y = Str2Int(sy@);
    let ghost m = Str2Int(sz@);
    let ghost result_nat = ModExp(x, y, m);
    Vec::from_seq(Int2Str(result_nat))
}
// </vc-code>

fn main() {}
}
