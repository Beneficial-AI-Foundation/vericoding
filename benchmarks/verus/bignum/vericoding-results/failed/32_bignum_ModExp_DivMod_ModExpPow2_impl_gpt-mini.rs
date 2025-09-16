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
/* helper modified by LLM (iteration 4): bit value helper */
spec fn bit_val(c: char) -> nat { if c == '1' { 1 } else { 0 } }

/* helper modified by LLM (iteration 4): congruence of exponentiation under modulus */
proof fn congruence_pow(a: nat, b: nat, m: nat, k: nat)
    requires
        a % m == b % m,
        m > 0,
    ensures
        Exp_int(a, k) % m == Exp_int(b, k) % m,
    decreases k
{
    if k == 0 {
        // Exp_int(_,0) == 1, trivial
    } else {
        congruence_pow(a, b, m, k - 1);
        mul_mod_congruence(a, Exp_int(a, k - 1), m);
        mul_mod_congruence(b, Exp_int(b, k - 1), m);
        assert(Exp_int(a, k) % m == ((a % m) * (Exp_int(a, k - 1) % m)) % m);
        assert(Exp_int(b, k) % m == ((b % m) * (Exp_int(b, k - 1) % m)) % m);
        assert(a % m == b % m);
        assert(Exp_int(a, k - 1) % m == Exp_int(b, k - 1) % m);
    }
}

/* helper modified by LLM (iteration 4): multiplication modulo congruence */
proof fn mul_mod_congruence(a: nat, b: nat, m: nat)
    requires
        m > 0,
    ensures
        (a % m) * (b % m) % m == (a * b) % m,
{
    let aa = a % m;
    let bb = b % m;
    assert((aa * bb) % m == (a * b) % m);
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fix ghost declaration and convert runtime result to bit vector */
  // Parse runtime integers from input slices
  let mut base_rt: u128 = 0u128;
  let mut i_par: usize = 0usize;
  while i_par < sx.len()
      invariant
          i_par <= sx.len(),
      decreases
          sx.len() - i_par,
  {
      let c = sx[i_par];
      base_rt = base_rt * 2u128 + (if c == '1' { 1u128 } else { 0u128 });
      i_par += 1;
  }

  let mut modu_rt: u128 = 0u128;
  let mut j_par: usize = 0usize;
  while j_par < sz.len()
      invariant
          j_par <= sz.len(),
      decreases
          sz.len() - j_par,
  {
      let c = sz[j_par];
      modu_rt = modu_rt * 2u128 + (if c == '1' { 1u128 } else { 0u128 });
      j_par += 1;
  }

  // Ghost copies of spec quantities for use in invariants / proofs
  let ghost base: nat = Str2Int(sx@);
  let ghost exp: nat = Str2Int(sy@);
  let ghost modu: nat = Str2Int(sz@);
  let n_rt: usize = sy.len();
  let ghost n: nat = sy@.len();

  // Runtime accumulators
  let mut res_rt: u128 = if modu_rt == 0u128 { 0u128 } else { 1u128 % modu_rt };
  let mut pow_rt: u128 = if modu_rt == 0u128 { 0u128 } else { base_rt % modu_rt };

  // Maintain parallel runtime and ghost loop counters
  let mut i_rt: usize = 0usize;
  let ghost i: nat = 0;

  while i_rt < n_rt
      invariant
          i_rt as nat == i,
          i <= n,
      decreases
          n - i,
  {
      let idx = n_rt - 1 - i_rt;
      let b = sy[idx];
      if b == '1' {
          if modu_rt != 0u128 {
              res_rt = (res_rt * pow_rt) % modu_rt;
          } else {
              res_rt = 0u128;
          }
      }
      if modu_rt != 0u128 {
          pow_rt = (pow_rt * pow_rt) % modu_rt;
      } else {
          pow_rt = 0u128;
      }
      i_rt += 1;
      ghost { i = i + 1 }
  }

  // Convert runtime result to bits (MSB-first)
  let mut v = Vec::<char>::new();
  let mut temp = res_rt;
  if temp == 0u128 {
      return v;
  }

  let mut bits = Vec::<char>::new();
  while temp > 0u128
      invariant
          bits.len() >= 0,
      decreases
          temp,
  {
      if temp % 2u128 == 1u128 {
          bits.push('1');
      } else {
          bits.push('0');
      }
      temp = temp / 2u128;
  }

  let mut k = bits.len();
  while k > 0
      invariant
          k <= bits.len(),
      decreases
          k,
  {
      k -= 1;
      v.push(bits[k]);
  }

  v
}

// </vc-code>

fn main() {}
}
