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
exec fn mod_pow(base: nat, exp: nat, m: nat) -> (res: nat)
  requires m > 0nat,
  ensures res == Exp_int(base, exp) % m,
  decreases exp
{
  /* helper modified by LLM (iteration 2): fixed type mismatches by using nat literals */
  if exp == 0nat {
    1nat
  } else {
    let half = mod_pow(base, exp / 2nat, m);
    let sq = (half * half) % m;
    if exp % 2nat == 1nat {
      ((sq * base) % m)
    } else {
      sq
    }
  }
}

spec fn bit_length(n: nat) -> int
  decreases n
{
  if n == 0nat {1nat} else { 1nat + bit_length(n / 2nat) }
}

exec fn nat_to_binary(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n,
{
  /* helper modified by LLM (iteration 2): fixed type mismatches by using nat literals */
  let mut vec = Vec::new();
  let mut temp = n;
  if temp == 0nat {
    vec.push('0');
    return vec;
  }
  while temp > 0nat
    invariant ValidBitString(vec@),
    decreases temp
  {
    if temp % 2nat == 1nat {
      vec.push('1');
    } else {
      vec.push('0');
    }
    temp = temp / 2nat;
  }
  vec.reverse();
  return vec;
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented modular exponentiation convert to binary string */
  let x = Str2Int(sx@);
  let y = Str2Int(sy@);
  let z = Str2Int(sz@);
  let res_num = mod_pow(x, y, z);
  let res = nat_to_binary(res_num);
  return res;
}
// </vc-code>

fn main() {}
}
