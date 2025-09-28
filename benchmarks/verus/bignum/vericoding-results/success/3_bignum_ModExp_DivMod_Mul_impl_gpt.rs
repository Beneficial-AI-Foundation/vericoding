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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@) &&
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(res.0@) && valid_bit_string(res.1@) &&
    str2int(res.0@) == str2int(dividend@) / str2int(divisor@) &&
    str2int(res.1@) == str2int(dividend@) % str2int(divisor@)
{
  assume(false);
  (Vec::new(), Vec::new())
}

fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
{
  assume(false);
  Vec::new()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix algebraic step in lemma_exp_add using nonlinear_arith to justify associativity/commutativity where needed */
proof fn lemma_exp_add(x: nat, a: nat, b: nat)
  ensures
    exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
  decreases b
{
  if b == 0nat {
    assert(exp_int(x, 0nat) == 1nat);
    assert(exp_int(x, a + 0nat) == exp_int(x, a));
    assert(exp_int(x, a) * 1nat == exp_int(x, a)) by(nonlinear_arith);
  } else {
    let b1 = (b - 1nat) as nat;
    lemma_exp_add(x, a, b1);
    assert(exp_int(x, b) == x * exp_int(x, b1));
    assert(exp_int(x, a + b) == x * exp_int(x, a + b1));
    assert(exp_int(x, a + b1) == exp_int(x, a) * exp_int(x, b1));
    assert(x * (exp_int(x, a) * exp_int(x, b1)) == exp_int(x, a) * (x * exp_int(x, b1))) by(nonlinear_arith);
    assert(exp_int(x, a) * (x * exp_int(x, b1)) == exp_int(x, a) * exp_int(x, b));
    assert(exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b));
  }
}

/* helper modified by LLM (iteration 4): clarify expansion for y=1 */
proof fn lemma_exp_one(x: nat)
  ensures exp_int(x, 1nat) == x
{
  assert(exp_int(x, 1nat) == x * exp_int(x, 0nat));
  assert(exp_int(x, 0nat) == 1nat);
  assert(x * 1nat == x) by(nonlinear_arith);
}

/* helper modified by LLM (iteration 4): exponentiation by bits; minor proof strengthening while preserving logic */
fn pow_bits(sx: Vec<char>, sy: Vec<char>, nz: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(sx@),
    valid_bit_string(sy@),
    valid_bit_string(nz@),
    str2int(nz@) > 0nat
  ensures
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@))
  decreases sy@.len()
{
  if sy.len() == 0 {
    let (q, _r) = div_mod(nz.clone(), nz);
    assert(str2int(q@) == str2int(nz@) / str2int(nz@));
    assert(str2int(q@) == 1nat);
    q
  } else {
    let last_index = sy.len() - 1usize;
    let last = sy[last_index];
    let mut prefix = sy.clone();
    let _popped = prefix.pop();

    let t = pow_bits(sx.clone(), prefix.clone(), nz.clone());
    let sq = mul(t.clone(), t);

    if last == '1' {
      let r1 = mul(sq.clone(), sx.clone());
      proof {
        let a = str2int(prefix@);
        assert(str2int(t@) == exp_int(str2int(sx@), a));
        assert(str2int(sq@) == str2int(t@) * str2int(t@));
        lemma_exp_add(str2int(sx@), a, a);
        assert(str2int(sq@) == exp_int(str2int(sx@), a + a));
        assert(str2int(r1@) == str2int(sq@) * str2int(sx@));
        lemma_exp_one(str2int(sx@));
        lemma_exp_add(str2int(sx@), a + a, 1nat);
      }
      r1
    } else {
      proof {
        let a = str2int(prefix@);
        assert(str2int(t@) == exp_int(str2int(sx@), a));
        assert(str2int(sq@) == str2int(t@) * str2int(t@));
        lemma_exp_add(str2int(sx@), a, a);
        assert(str2int(sq@) == exp_int(str2int(sx@), a + a));
      }
      sq
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute power via helper pow_bits, then take modulo using div_mod and return remainder */
  let pow = pow_bits(sx.clone(), sy.clone(), sz.clone());
  let (_q, r) = div_mod(pow, sz);
  r
}
// </vc-code>


}

fn main() {}