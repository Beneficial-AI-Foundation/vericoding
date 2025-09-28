// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn one_bit_string() -> Vec<char> { vec!['1'] }

fn bit_string_to_u128(s: Vec<char>) -> (res: u128)
  requires
    valid_bit_string(s@),
  ensures
    res == str2int(s@) as u128,
{
  let mut res = 0u128;
  for i in 0..s.len() {
    res = res * 2;
    if s[i] == '1' {
      res += 1;
    }
  }
  res
}

/* helper modified by LLM (iteration 2): replaced reverse() with manual reversal loop */
fn u128_to_bit_string(n: u128) -> (res: Vec<char>)
  ensures
    valid_bit_string(res@),
    str2int(res@) == n as nat,
{
  if n == 0 {
    vec!['0']
  } else {
    let mut res = Vec::new();
    let mut current = n;
    while current > 0
      invariant
        n % (2u128 << (res.len() as u32)) == current,
        str2int(res@) == (n / (2u128 << (res.len() as u32))) as nat,
    {
      res.push(if current % 2 == 1 { '1' } else { '0' });
      current /= 2;
    }
    // Manual reversal
    let mut reversed = Vec::with_capacity(res.len());
    for i in 0..res.len() {
        reversed.push(res[res.len() - 1 - i]);
    }
    reversed
  }
}

fn mod_bit_string(a: Vec<char>, m: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(m@),
    str2int(m@) > 1,
  ensures
    valid_bit_string(res@),
    str2int(res@) == str2int(a@) % str2int(m@),
{
  let a_int = bit_string_to_u128(a);
  let m_int = bit_string_to_u128(m);
  let r = a_int % m_int;
  u128_to_bit_string(r)
}

fn multiply_bit_string(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@),
  ensures
    valid_bit_string(res@),
    str2int(res@) == str2int(a@) * str2int(b@),
{
  let a_int = bit_string_to_u128(a);
  let b_int = bit_string_to_u128(b);
  let product = a_int * b_int;
  u128_to_bit_string(product)
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 6): fixed slicing error by replacing slice operation with manual loop */
  if sy.len() == 1 {
    if sy[0] == '0' {
      one_bit_string()
    } else {
      mod_bit_string(sx, sz)
    }
  } else {
    let last_char = sy[sy.len()-1];
    let mut sy_rest = Vec::with_capacity(sy.len() - 1);
    for i in 0..sy.len()-1 {
        sy_rest.push(sy[i]);
    }

    let sx_squared = multiply_bit_string(sx.clone(), sx.clone());
    let sx_squared_mod = mod_bit_string(sx_squared, sz);

    let part1 = mod_exp(sx_squared_mod, sy_rest, sz);

    let factor = if last_char == '1' { sx.clone() } else { one_bit_string() };

    let part2 = multiply_bit_string(part1, factor);
    let result = mod_bit_string(part2, sz);

    result
  }
}
// </vc-code>


}

fn main() {}