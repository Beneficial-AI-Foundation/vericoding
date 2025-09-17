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
exec fn compute_str2int(s: &[char]) -> int
  requires
    ValidBitString(s@),
  decreases
    s.len(),
  ensures
    result as nat == Str2Int(s@),
{
  let mut result = 0;
  let mut i = 0;
  while i < s.len()
    invariant
      0 <= result,
      result as nat == Str2Int(s@.subrange(0, i as int)),
      decreases
        s.len() - i,
  {
    let bit = if s[i] == '1' { 1 } else { 0 };
    result = result * 2 + bit;
    i = i + 1;
  }
  result
}

exec fn to_binary_string(n: int, len: usize) -> Vec<char>
  requires
    0 <= n && n <= ((1 << len) - 1),
  ensures
    ValidBitString(result@),
    Str2Int(result@) == n as nat,
{
  let mut s = Vec::new();
  let mut i = len as int - 1;
  while i >= 0
    invariant
      s.len() == (len as int - 1 - i),
      0 <= i || n == 0 && s.len() == len as int,
      decreases
        i,
  {
    s.push(if (n >> i) & 1 == 1 { '1' } else { '0' });
    i = i - 1;
  }
  s
}

exec fn mod_mul(a: &[char], b: &[char], m: &[char]) -> Vec<char>
  requires
    ValidBitString(a@), ValidBitString(b@), ValidBitString(m@), Str2Int(m@) > 1,
  ensures
    ValidBitString(result@),
    Str2Int(result@) == Str2Int(a@) * Str2Int(b@) % Str2Int(m@),
{
  let a_int = compute_str2int(a);
  let b_int = compute_str2int(b);
  let m_int = compute_str2int(m);
  let prod = a_int * b_int;
  let mod_result = prod % m_int;
  to_binary_string(mod_result, m.len())
}

/* helper modified by LLM (iteration 4): fixed syntax for spec blocks using logical AND instead of comma-separated to resolve compilation error */
exec fn mod_exp(b: &[char], e: &[char], m: &[char]) -> (res: Vec<char>)
  requires
    ValidBitString(b@) && ValidBitString(e@) && ValidBitString(m@) && m@.len() > 0 && Str2Int(m@) > 1,
  ensures
    ValidBitString(res@) && Str2Int(res@) == Exp_int(Str2Int(b@), Str2Int(e@)) % Str2Int(m@),
  decreases
    e@.len(),
{
  if e.len() == 0 {
    vec!['1']
  } else if e[e.len() - 1] == '0' {
    let half_pow = mod_exp(b, &e[..e.len() - 1], m);
    half_pow
  } else {
    let half_pow = mod_exp(b, &e[..e.len() - 1], m);
    let square = mod_mul(&half_pow, &half_pow, m);
    let result = mod_mul(&square, b, m);
    result
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
    /* code modified by LLM (iteration 4): called the helper function mod_exp to compute the result */
    let result = mod_exp(sx, sy, sz);
    result
}
// </vc-code>

fn main() {}
}
