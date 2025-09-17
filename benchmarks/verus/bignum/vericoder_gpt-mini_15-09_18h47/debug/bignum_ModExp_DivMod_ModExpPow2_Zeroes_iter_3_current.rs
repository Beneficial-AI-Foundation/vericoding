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
/* helper modified by LLM (iteration 3): bounds for Str2Int */
proof fn Str2Int_bounds(s: Seq<char>) ensures Str2Int(s) < Exp_int(2, s.len() as nat) decreases s.len() {
    if s.len() == 0 {
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        Str2Int_bounds(prefix);
        let bit = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2nat * Str2Int(prefix) + bit);
        assert(Str2Int(prefix) < Exp_int(2, prefix.len() as nat));
        assert(Str2Int(prefix) + 1 <= Exp_int(2, prefix.len() as nat));
        assert(2nat * (Str2Int(prefix) + 1) <= 2nat * Exp_int(2, prefix.len() as nat));
        assert(2nat * Str2Int(prefix) + bit < 2nat * Exp_int(2, prefix.len() as nat));
        assert(Exp_int(2, s.len() as nat) == 2nat * Exp_int(2, prefix.len() as nat));
    }
}

/* helper modified by LLM (iteration 3): positivity of powers of two */
proof fn pow2_positive(n: nat) ensures Exp_int(2, n) > 0 decreases n {
    if n == 0 {
        assert(Exp_int(2, 0) == 1nat);
    } else {
        pow2_positive(n - 1);
        assert(Exp_int(2, n) == 2nat * Exp_int(2, n - 1));
        assert(Exp_int(2, n - 1) > 0);
        assert(2nat * Exp_int(2, n - 1) > 0);
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
  /* code modified by LLM (iteration 3): fixed nat/int literal types and parsing/modexp/output */

  // Parse sx into x_nat
  let lx: usize = sx.len();
  let mut ix: usize = 0;
  let mut x_nat: nat = 0nat;
  while ix < lx
      invariant
          ix <= lx,
          x_nat == Str2Int(sx@.subrange(0, ix as int)),
      decreases lx - ix
  {
      let c = sx[ix];
      if c == '1' {
          x_nat = 2nat * x_nat + 1nat;
      } else {
          x_nat = 2nat * x_nat;
      }
      ix += 1;
  }

  // Parse sy into y_nat
  let ly: usize = sy.len();
  let mut iy: usize = 0;
  let mut y_nat: nat = 0nat;
  while iy < ly
      invariant
          iy <= ly,
          y_nat == Str2Int(sy@.subrange(0, iy as int)),
      decreases ly - iy
  {
      let c = sy[iy];
      if c == '1' {
          y_nat = 2nat * y_nat + 1nat;
      } else {
          y_nat = 2nat * y_nat;
      }
      iy += 1;
  }

  // Parse sz into m_nat
  let lz: usize = sz.len();
  let mut iz: usize = 0;
  let mut m_nat: nat = 0nat;
  while iz < lz
      invariant
          iz <= lz,
          m_nat == Str2Int(sz@.subrange(0, iz as int)),
      decreases lz - iz
  {
      let c = sz[iz];
      if c == '1' {
          m_nat = 2nat * m_nat + 1nat;
      } else {
          m_nat = 2nat * m_nat;
      }
      iz += 1;
  }

  // Modular exponentiation scanning bits of y (MSB to LSB)
  let mut res_nat: nat = 1nat % m_nat;
  let x_mod: nat = x_nat % m_nat;
  let mut j: usize = 0;
  while j < ly
      invariant
          j <= ly,
          res_nat == Exp_int(x_nat, Str2Int(sy@.subrange(0, j as int))) % m_nat,
      decreases ly - j
  {
      // square
      let tmp = (res_nat * res_nat) % m_nat;
      res_nat = tmp;
      if sy[j] == '1' {
          res_nat = (res_nat * x_mod) % m_nat;
      }
      j += 1;
  }

  // Build output bitstring of length lz representing res_nat (MSB-first), padded with leading zeros
  let L: usize = lz;
  // compute pow = 2^(L-1)
  let mut pow: nat = 1nat;
  if L > 0 {
      let mut k: usize = 0;
      while k < L - 1
          invariant
              k <= L - 1,
              pow == Exp_int(2, k as nat),
          decreases (L - 1) - k
      {
          pow = pow * 2nat;
          k += 1;
      }
  }

  let mut out: Vec<char> = Vec::<char>::new();
  let mut rem: nat = res_nat;
  let mut idx: usize = 0;
  while idx < L
      invariant
          idx <= L,
      decreases L - idx
  {
      if rem >= pow {
          out.push('1');
          rem = rem - pow;
      } else {
          out.push('0');
      }
      // integer division by 2
      if pow > 0nat {
          pow = pow / 2nat;
      } else {
          pow = 0nat;
      }
      idx += 1;
  }

  return out;
}

// </vc-code>

fn main() {}
}
