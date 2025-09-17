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
/* helper modified by LLM (iteration 4): convert bit slice to u128 */
fn run_Str2Int_u128(s: &[char]) -> u128 {
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    while i < s.len() {
        acc = acc * 2 + (if s[i] == '1' { 1u128 } else { 0u128 });
        i += 1;
    }
    acc
}

/* helper modified by LLM (iteration 4): convert u128 to bit Vec<char> (MSB..LSB) */
fn u128_to_bits(mut n: u128) -> Vec<char> {
    let mut rev = Vec::<char>::new();
    while n > 0 {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        rev.push(bit);
        n /= 2;
    }
    if rev.len() == 0 {
        let mut v = Vec::<char>::new();
        v.push('0');
        return v;
    }
    let mut v = Vec::<char>::new();
    let mut i: usize = rev.len();
    while i > 0 {
        i -= 1;
        v.push(rev[i]);
    }
    v
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
  /* code modified by LLM (iteration 4): modular exponentiation using u128 runtime arithmetic */
  let x = run_Str2Int_u128(sx);
  let m = run_Str2Int_u128(sz);
  let mut base: u128 = if m != 0 { x % m } else { 0 };
  let mut res_nat: u128 = if m != 0 { 1 % m } else { 0 };
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
          res_nat = (res_nat * base) % m;
      }
      base = (base * base) % m;
      i += 1;
  }
  let res = u128_to_bits(res_nat);
  res
}
// </vc-code>

fn main() {}
}
