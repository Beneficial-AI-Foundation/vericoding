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
exec fn mod_exp(b: &[char], e: &[char], m: &[char]) -> Vec<char>
    requires
        ValidBitString(b@),
        ValidBitString(e@),
        ValidBitString(m@),
        m@.len() > 0,
        Str2Int(m@) > 1,
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Exp_int(Str2Int(b@), Str2Int(e@)) % Str2Int(m@),
    decreases e@.len()
{
    if e.len() == 0 {
        vec!['1']
    } else if e[e.len() - 1] == '0' {
        let half_pow = mod_exp(b, &e[..e.len() - 1], m);
        half_pow
    } else {
        let half_pow = mod_exp(b, &e[..e.len() - 1], m);
        vec!['1']
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let result = mod_exp(sx, sy, sz);
    result
}
// </vc-code>

fn main() {}
}
