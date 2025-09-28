// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): executable helpers using Rust numeric and index types (usize/u128) to avoid spec-only nat/int types */
fn seq_to_int_exec(s: Seq<char>) -> u128
  requires valid_bit_string(s)
  decreases s.len()
{
    let mut r: u128 = 0u128;
    let mut i: usize = 0usize;
    let len_usize: usize = (s.len() as int) as usize;
    while i < len_usize
        invariant
            i <= len_usize,
        decreases len_usize - i
    {
        let ch: char = s[i as int];
        let bit: u128 = if ch == '1' { 1u128 } else { 0u128 };
        r = r * 2u128 + bit;
        i = i + 1usize;
    }
    r
}

/* helper modified by LLM (iteration 10): modular exponentiation using u128 arithmetic */
fn powmod_exec(mut base: u128, mut exp: u128, modu: u128) -> u128
  requires modu > 0u128
  decreases exp
{
    base = base % modu;
    let mut res: u128 = 1u128 % modu;
    while exp > 0u128
        invariant
            modu > 0u128,
        decreases exp
    {
        if exp % 2u128 == 1u128 {
            res = (res * base) % modu;
        }
        base = (base * base) % modu;
        exp = exp / 2u128;
    }
    res
}

/* helper modified by LLM (iteration 10): build Seq<char> bit-string of given length from numeric value (u128) */
fn int_to_bits_exec(mut n: u128, len: usize) -> (result: Seq<char>)
  decreases len
{
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < len
        invariant
            i <= len,
        decreases len - i
    {
        let bit_ch: char = if n % 2u128 == 1u128 { '1' } else { '0' };
        v.push(bit_ch);
        n = n / 2u128;
        i = i + 1usize;
    }
    v.reverse();
    vstd::seq::Seq::from(v)
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): compute modular exponent using executable helpers (usize/u128) and return bit-sequence */
  let base = seq_to_int_exec(sx);
  let exp = seq_to_int_exec(sy);
  let modu = seq_to_int_exec(sz);
  let r = powmod_exec(base, exp, modu);
  int_to_bits_exec(r, (sz.len() as int) as usize)
}

// </vc-code>


}

fn main() {}