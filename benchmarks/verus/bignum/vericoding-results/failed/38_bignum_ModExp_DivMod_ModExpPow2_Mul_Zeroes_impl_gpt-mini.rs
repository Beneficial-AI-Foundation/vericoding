// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(result.0) && valid_bit_string(result.1),
    str2int(result.0) == str2int(dividend) / str2int(divisor),
    str2int(result.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
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
/* helper modified by LLM (iteration 10): spec helpers for zero sequences, nat->bits conversion, and modular pow */
spec fn zeros_seq(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 { Seq::<char>::empty() } else { zeros_seq((n - 1) as nat) + Seq::<char>::new(1, |i: int| '0') }
}

spec fn nat_to_bits_rec(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 { Seq::<char>::empty() } else { let prev = nat_to_bits_rec(n / 2); let c = if n % 2 == 1 { '1' } else { '0' }; prev + Seq::<char>::new(1, |i: int| c) }
}

spec fn nat_to_bits_with_len(n: nat, len: nat) -> Seq<char>
  decreases len
{
  let s = if n == 0 { Seq::<char>::new(1, |i: int| '0') } else { nat_to_bits_rec(n) };
  if (s.len() as nat) >= len { s } else { let diff: int = (len as int) - s.len(); zeros_seq(diff as nat) + s }
}

spec fn pow_mod_nat(base: nat, exp: nat, m: nat) -> nat
  decreases exp
{
  if m == 0 { 0nat } else if exp == 0 { 1nat % m } else {
    let half = pow_mod_nat(base, exp / 2, m);
    let full = (half * half) % m;
    if exp % 2 == 0 { full } else { (full * (base % m)) % m }
  }
}

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): compute modular exponent via spec pow_mod and convert to fixed-length bit sequence */
  let r: nat = pow_mod_nat(str2int(sx), str2int(sy), str2int(sz));
  let res_spec: Seq<char> = nat_to_bits_with_len(r, (sz.len() as nat));
  res_spec
}

// </vc-code>


}

fn main() {}