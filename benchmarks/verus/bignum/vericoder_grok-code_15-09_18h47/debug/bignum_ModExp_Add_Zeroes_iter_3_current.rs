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
exec fn str2nat(s: &Vec<char>) -> nat
decreases s.len()
{
  if s.len() == 0 { 0 as nat } else { (2 as nat) * str2nat(&s[..s.len() - 1].to_vec()) + (if s[s.len() - 1] == '1' {1 as nat} else {0 as nat}) }
}
/* helper modified by LLM (iteration 3): fixed invalid nat suffixes by replacing them with integer literals and adding as nat casts */
exec fn nat2bits(n: nat) -> Vec<char>
decreases n
{
  if n == (0 as nat) { Vec::new() } else {
    let mut v = nat2bits(n / (2 as nat));
    v.push(if n % (2 as nat) == (0 as nat) { '0' } else { '1' });
    v
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed invalid nat suffixes by replacing them with integer literals and adding as nat casts for type compatibility */
{
  if sy@.len() == (0 as nat) {
    return nat2bits(1 as nat);
  }
  let mut sy_short = sy.to_vec();
  sy_short.remove(sy_short.len() - 1);
  let sub_res = ModExp_Add_Zeroes(sx, &sy_short, sz);
  let a = str2nat(&sub_res);
  let m = str2nat(&sz.to_vec());
  if sy[sy.len() - 1] == '0' {
    let b = str2nat(&sub_res);
    let sq_mod = (a * b) % m;
    return nat2bits(sq_mod);
  } else {
    let x = str2nat(&sx.to_vec());
    let sq = a * a;
    let mul_mod = (sq * x) % m;
    return nat2bits(mul_mod);
  }
}
// </vc-code>

fn main() {}
}
