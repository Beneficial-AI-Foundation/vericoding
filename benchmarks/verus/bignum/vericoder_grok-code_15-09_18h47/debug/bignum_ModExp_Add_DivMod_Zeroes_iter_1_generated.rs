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
exec fn bin_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures bin_to_nat(s) == Str2Int(s@)
  decreases s@.len()
{
    if s.len() == 0 { 0 } else {
        let high = &s[0..s.len()-1];
        let sub = bin_to_nat(high);
        let low = s[s.len()-1];
        2 * sub + if low == '1' { 1 } else { 0 }
    }
}

exec fn modpow(base: nat, exp: nat, mod: nat) -> nat
  requires mod > 1, exp >= 0
  ensures modpow(base, exp, mod) == Exp_int(base, exp) % mod
  decreases exp
{
  if exp == 0 { 1 } else {
    let b2 = base * base % mod;
    let p = modpow(b2, exp / 2, mod);
    if exp % 2 == 0 {
      p % mod
    } else {
      p * base % mod % mod
    }
  }
}

exec fn nat_to_bin(n: nat) -> Vec<char>
  ensures ValidBitString(res@), Str2Int(res@) == n
{
  if n == 0 { Vec::<char>::with_capacity(0) } else {
    let mut bin = Vec::<char>::new();
    let mut num = n;
    while num > 0 {
      bin.push(if num % 2 == 0 { '0' } else { '1' });
      num = num / 2;
    }
    bin.reverse();
    bin
  }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  let x_int = bin_to_nat(sx);
  let y_int = bin_to_nat(sy);
  let z_int = bin_to_nat(sz);
  let res_int = modpow(x_int, y_int, z_int);
  let res = nat_to_bin(res_int);
  res
}
// </vc-code>

fn main() {}
}
