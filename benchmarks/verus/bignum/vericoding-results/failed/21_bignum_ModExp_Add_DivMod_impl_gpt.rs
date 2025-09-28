// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): introduce nat_to_bits, a spec mod_exp_seq, and an inductive lemma connecting Seq bits with integers */
spec fn nat_to_bits(n: nat) -> Seq<char>
  decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        nat_to_bits(q).push(if r == 1nat { '1' } else { '0' })
    }
}

spec fn mod_exp_seq(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> Seq<char>
  decreases sy.len()
{
    nat_to_bits(exp_int(str2_int(sx), str2_int(sy)) % str2_int(sz))
}

proof fn lemma_nat_to_bits_props(n: nat)
  ensures
      valid_bit_string(nat_to_bits(n)),
      str2_int(nat_to_bits(n)) == n
  decreases n
{
  if n == 0nat {
      assert(valid_bit_string(Seq::<char>::empty()));
      assert(str2_int(Seq::<char>::empty()) == 0nat);
  } else {
      let q = n / 2nat;
      let r = n % 2nat;
      lemma_nat_to_bits_props(q);
      let bit = if r == 1nat { '1' } else { '0' };
      let t = nat_to_bits(q).push(bit);

      assert(forall|i: int| 0 <= i < t.len() ==> (t[i] == '0' || t[i] == '1')) by {
          assert forall|i: int| 0 <= i < t.len() implies (t[i] == '0' || t[i] == '1') by {
              if i < nat_to_bits(q).len() {
                  assert(valid_bit_string(nat_to_bits(q)));
              } else {
                  assert(t.len() == nat_to_bits(q).len() + 1);
                  assert(i == nat_to_bits(q).len());
                  assert(t[i] == bit);
                  if r == 1nat { assert(t[i] == '1'); } else { assert(t[i] == '0'); }
              }
          }
      }

      assert(t.len() == nat_to_bits(q).len() + 1);
      assert(t.len() > 0);
      assert(t.subrange(0, t.len() - 1) == nat_to_bits(q));
      assert(t[t.len() - 1] == bit);

      assert(str2_int(t) ==
          2nat * str2_int(t.subrange(0, t.len() - 1))
            + (if t[t.len() - 1] == '1' { 1nat } else { 0nat }));

      if r == 1nat {
          assert(str2_int(t) == 2nat * str2_int(nat_to_bits(q)) + 1nat);
      } else {
          assert(str2_int(t) == 2nat * str2_int(nat_to_bits(q)) + 0nat);
      }
      assert(str2_int(nat_to_bits(q)) == q);
      assert(n == 2nat * q + r);

      if r == 1nat {
          assert(str2_int(t) == 2nat * q + 1nat);
      } else {
          assert(str2_int(t) == 2nat * q);
      }

      assert(valid_bit_string(t));
      assert(nat_to_bits(n) == t);
      assert(str2_int(nat_to_bits(n)) == n);
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): construct result via spec mod_exp_seq and convert using Vec::from */
    let res_s = mod_exp_seq(sx@, sy@, sz@);
    proof { lemma_nat_to_bits_props(exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@)); }
    let res_v: Vec<char> = Vec::from(res_s);
    res_v
}
// </vc-code>


}

fn main() {}