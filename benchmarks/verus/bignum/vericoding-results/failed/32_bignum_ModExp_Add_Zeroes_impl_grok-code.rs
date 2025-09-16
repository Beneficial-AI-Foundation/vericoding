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
/* helper modified by LLM (iteration 10): changed parameter to &[char] to avoid to_vec() compilation error */
exec fn str2nat(s: &[char]) -> u64 {
  let mut result: u64 = 0;
  let mut i = 0;
  while i < s.len()
      invariant
          i <= s.len(),
          result >= 0
  {
    result = result * 2 + (if s[i] == '1' { 1u64 } else { 0u64 });
    i = i + 1;
  }
  result
}
/* helper modified by LLM (iteration 9): same as previous */
exec fn nat2bits(n: u64) -> Vec<char>
decreases n
{
  if n == 0 { Vec::new() } else {
    let mut v = nat2bits(n / 2 );
    v.push(if (n % 2 ) == 0 { '0' } else { '1' });
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
{
    /* code modified by LLM (iteration 10): fixed compilation by removing to_vec(), passing &[char] directly */
    if sy.is_empty() {
        return vec!['1'];
    }
    let sub_sy = &sy[..sy.len() - 1];
    let sub_res = ModExp_Add_Zeroes(sx, sub_sy, sz);
    let a = str2nat(&sub_res);
    let m = str2nat(sz);
    if sy[sy.len() - 1] == '0' {
        let sq = (a as u128) * (a as u128);
        let sq_mod = (sq % (m as u128)) as u64;
        return nat2bits(sq_mod);
    } else {
        let x = str2nat(sx);
        let sq = (a as u128) * (a as u128);
        let sq_mod = sq % (m as u128);
        let mul = (sq_mod * (x as u128)) % (m as u128);
        let mul_mod = mul as u64;
        return nat2bits(mul_mod);
    }
}
// </vc-code>

fn main() {}
}
