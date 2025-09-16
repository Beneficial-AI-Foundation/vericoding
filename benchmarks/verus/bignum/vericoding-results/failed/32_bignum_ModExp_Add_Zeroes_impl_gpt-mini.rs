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
/* helper modified by LLM (iteration 10): convert bit slice to u128 preserving Str2Int for subranges */
exec fn run_Str2Int_u128(s: &[char]) -> (res: u128)
    requires
        ValidBitString(s@),
    ensures
        (res as nat) == Str2Int(s@),
    decreases
        s.len()
{
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            (acc as nat) == Str2Int(s@.subrange(0, i as int)),
            forall |k: int| 0 <= k && k < i as int ==> (s.index(k) == '0' || s.index(k) == '1'),
        decreases
            s.len() - i
    {
        let bit = if s[i] == '1' { 1u128 } else { 0u128 };
        acc = acc * 2 + bit;
        i += 1;
    }
    acc
}

/* helper modified by LLM (iteration 10): convert u128 to bit Vec<char> (MSB..LSB) with usize indices */
exec fn u128_to_bits(n0: u128) -> (v: Vec<char>)
    ensures
        Str2Int(v@) == (n0 as nat),
        ValidBitString(v@),
    decreases
        n0
{
    let mut n = n0;
    let mut rev = Vec::<char>::new();
    if n == 0 {
        let mut z = Vec::<char>::new();
        z.push('0');
        return z;
    }
    while n != 0u128
        invariant
            forall |i: int| 0 <= i && i < rev@.len() as int ==> (rev@.index(i) == '0' || rev@.index(i) == '1'),
        decreases
            n
    {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        rev.push(bit);
        n /= 2;
    }
    let mut vfinal = Vec::<char>::new();
    let mut j: usize = rev.len();
    while j > 0
        invariant
            j <= rev.len(),
            vfinal@.len() as int + j as int == rev@.len() as int,
            forall |k: int| 0 <= k && k < vfinal@.len() as int ==> (vfinal@.index(k) == '0' || vfinal@.index(k) == '1'),
        decreases
            j
    {
        j -= 1;
        vfinal.push(rev[j]);
    }
    proof {
        assert(vfinal@.len() as int == rev@.len() as int);
    }
    vfinal
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): modular exponentiation implemented using helpers with corrected integer types */
  let x = run_Str2Int_u128(sx);
  let m = run_Str2Int_u128(sz);
  proof {
    assert(ValidBitString(sx@));
    assert(ValidBitString(sz@));
    assert((m as nat) == Str2Int(sz@));
    assert(Str2Int(sz@) > 1);
  }
  let mut base: u128 = x % m;
  let mut res_nat: u128 = 1u128 % m;
  let len = sy.len();
  let mut i: usize = 0;
  while i < len
      invariant
          i <= len,
      decreases
          len - i
  {
      let idx = len - 1 - i;
      if sy[idx] == '1' {
          let mut a = base;
          let mut b = res_nat;
          let mut prod: u128 = 0u128;
          let mut bit_idx: usize = 0;
          proof { assert(m != 0u128); }
          while bit_idx < 128 && b != 0u128
              invariant
                  bit_idx <= 128,
                  prod < m,
              decreases
                  128 - bit_idx
          {
              if (b & 1u128) == 1u128 {
                  prod = (prod + a) % m;
              }
              a = (a + a) % m;
              b = b >> 1;
              bit_idx += 1;
          }
          res_nat = prod % m;
      }
      {
          let mut a = base;
          let mut b = base;
          let mut prod2: u128 = 0u128;
          let mut bit_idx2: usize = 0;
          proof { assert(m != 0u128); }
          while bit_idx2 < 128 && b != 0u128
              invariant
                  bit_idx2 <= 128,
                  prod2 < m,
              decreases
                  128 - bit_idx2
          {
              if (b & 1u128) == 1u128 {
                  prod2 = (prod2 + a) % m;
              }
              a = (a + a) % m;
              b = b >> 1;
              bit_idx2 += 1;
          }
          base = prod2 % m;
      }
      i += 1;
  }
  let res = u128_to_bits(res_nat);
  res
}
// </vc-code>

fn main() {}
}
