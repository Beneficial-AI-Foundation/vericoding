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
/* helper modified by LLM (iteration 8): fixed type mismatches by using nat literals */exec fn bin_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures bin_to_nat(s) == Str2Int(s@)
  decreases s@.len()
{
    if s.len() == 0 { 0nat } else {
        let high = &s[0..s.len()-1];
        let sub = bin_to_nat(high);
        let low = s[s.len()-1];
        2nat * sub + if low == '1' { 1nat } else { 0nat }
    }
}

/* helper modified by LLM (iteration 8): fixed type mismatches by using nat literals */exec fn modpow(base: nat, exp: nat, m: nat) -> nat
  requires m > 1, exp >= 0nat
  ensures modpow(base, exp, m) == Exp_int(base, exp) % m
  decreases exp
{
  if exp == 0nat { 1nat } else {
    let b2 = base * base % m;
    let p = modpow(b2, exp / 2nat, m);
    if exp % 2nat == 0nat {
      p % m
    } else {
      p * base % m
    }
  }
}

/* helper modified by LLM (iteration 8): fixed type mismatches by using nat literals */exec fn nat_to_bin(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n
{
  if n == 0nat { vec!['0'] } else {
    let mut bin = Vec::<char>::new();
    let mut num = n;
    while num > 0nat
        invariant
            ValidBitString(bin@),
            Str2Int(bin@) == n - num,
        decreases num
    {
      bin.push(if num % 2nat == 0nat { '0' } else { '1' });
      num = num / 2nat;
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
/* code modified by LLM (iteration 8): implementation unchanged as errors were in helpers */
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
