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
/* helper modified by LLM (iteration 6): fixed type mismatches by adding nat suffixes to integer literals */
fn powmod(base: nat, exp: nat, m: nat) -> (res: nat)
    requires m > 0nat
    ensures res == Exp_int(base, exp) % m
    decreases exp
{
    if exp == 0nat {
        1nat
    } else {
        let half_exp = exp / 2nat;
        let bb_mod = ((base % m) * (base % m)) % m;
        let p = powmod(bb_mod, half_exp, m);
        let result = if exp % 2nat == 0nat { p } else { ((p * (base % m)) % m) % m };
        result
    }
}

/* helper modified by LLM (iteration 6): fixed type mismatches by adding nat suffixes to integer literals */
fn nat2vec(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    if n == 0nat {
        Vec::<char>::new()
    } else {
        let mut v = nat2vec(n / 2nat);
        v.push(if n % 2nat == 1nat { '1' } else { '0' });
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): no changes needed as type mismatches are in helpers */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let m_val = Str2Int(sz@);
    let res_val = powmod(x_val, y_val, m_val);
    nat2vec(res_val)
}
// </vc-code>

fn main() {}
}
