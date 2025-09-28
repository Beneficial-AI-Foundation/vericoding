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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1),
    str2int(ret.0) == str2int(dividend) / str2int(divisor),
    str2int(ret.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_exp_double(x: nat, k: nat)
  ensures exp_int(x, 2nat * k) == exp_int(x, k) * exp_int(x, k)
  decreases k
{
  if k == 0 {
    assert(exp_int(x, 0nat) == 1nat);
  } else {
    let k1 = (k - 1) as nat;
    lemma_exp_double(x, k1);
    assert(exp_int(x, 2nat * k) == x * exp_int(x, (2nat * k - 1) as nat));
    assert(exp_int(x, (2nat * k - 1) as nat) == x * exp_int(x, (2nat * k - 2) as nat));
    assert(2nat * k - 2 == 2nat * k1);
    assert(exp_int(x, 2nat * k) == (x * x) * exp_int(x, 2nat * k1));
    assert(exp_int(x, 2nat * k1) == exp_int(x, k1) * exp_int(x, k1));
    assert(exp_int(x, 2nat * k) == (x * x) * (exp_int(x, k1) * exp_int(x, k1)));
    assert(exp_int(x, k) == x * exp_int(x, k1));
    assert((x * x) * (exp_int(x, k1) * exp_int(x, k1)) == (x * exp_int(x, k1)) * (x * exp_int(x, k1)));
    assert(exp_int(x, 2nat * k) == exp_int(x, k) * exp_int(x, k));
  }
}

proof fn lemma_str2int_snoc(s: Seq<char>)
  requires
    valid_bit_string(s),
    s.len() > 0
  ensures
    str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
{
  assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
}

fn one() -> (s: Seq<char>)
  ensures
    s.len() == 1,
    valid_bit_string(s),
    str2int(s) == 1nat
{
  let s_local = seq!['1'];
  proof {
    assert(s_local.len() == 1);
    assert(str2int(s_local) == 2nat * str2int(s_local.subrange(0, 0)) + 1nat);
    assert(s_local.subrange(0, 0).len() == 0);
    assert(str2int(s_local.subrange(0, 0)) == 0nat);
  }
  s_local
}

/* helper modified by LLM (iteration 4): remove explicit int casts/locals; inline len/indexing to avoid ghost-int locals while keeping exponentiation-by-squaring */
fn pow_seq(sx: Seq<char>, sy: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy),
    sy.len() > 0
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy))
  decreases sy.len()
{
  if sy.len() == 1 {
    if sy[0] == '0' {
      let one_seq = one();
      one_seq
    } else {
      sx
    }
  } else {
    let t = pow_seq(sx, sy.subrange(0, sy.len() - 1));
    let sq = mul(t, t);
    if sy[sy.len() - 1] == '1' {
      mul(sq, sx)
    } else {
      sq
    }
  }
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
  /* code modified by LLM (iteration 4): compute power via helper and then reduce modulo using div_mod */
  let p = pow_seq(sx, sy);
  let dm = div_mod(p, sz);
  dm.1
}
// </vc-code>


}

fn main() {}