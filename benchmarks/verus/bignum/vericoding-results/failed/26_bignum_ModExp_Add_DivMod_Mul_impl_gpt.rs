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

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1) &&
    str2int(ret.0) == str2int(dividend) / str2int(divisor) &&
    str2int(ret.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): lemma for exponent addition */
proof fn lemma_exp_add(x: nat, y: nat, z: nat)
  ensures
    exp_int(x, y + z) == exp_int(x, y) * exp_int(x, z),
  decreases y
{
    if y == 0nat {
        assert(0nat + z == z) by(nonlinear_arith);
        assert(exp_int(x, 0nat + z) == exp_int(x, z));
        assert(exp_int(x, 0nat) == 1nat);
        assert(1nat * exp_int(x, z) == exp_int(x, z)) by(nonlinear_arith);
    } else {
        let y1 = (y - 1) as nat;
        lemma_exp_add(x, y1, z);
        assert(exp_int(x, y + z) == x * exp_int(x, ((y + z) - 1) as nat));
        assert(((y + z) - 1) as nat == y1 + z) by(nonlinear_arith);
        assert(exp_int(x, y + z) == x * exp_int(x, y1 + z));
        assert(exp_int(x, y1 + z) == exp_int(x, y1) * exp_int(x, z));
        assert(x * (exp_int(x, y1) * exp_int(x, z)) == (x * exp_int(x, y1)) * exp_int(x, z)) by(nonlinear_arith);
        assert(exp_int(x, y) == x * exp_int(x, y1));
        assert(exp_int(x, y + z) == (x * exp_int(x, y1)) * exp_int(x, z));
        assert((x * exp_int(x, y1)) * exp_int(x, z) == exp_int(x, y) * exp_int(x, z));
    }
}

/* helper modified by LLM (iteration 9): str2int snoc characterization for non-empty sequences */
proof fn lemma_str2int_snoc(s: Seq<char>)
  ensures
    s.len() > 0 ==> str2int(s) == 2nat * str2int(s.subrange(0int, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }),
  decreases s.len()
{
    if s.len() > 0 {
        assert(str2int(s) == 2nat * str2int(s.subrange(0int, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
    }
}

/* helper modified by LLM (iteration 9): lemma that exp(x,1) == x */
proof fn lemma_exp_one(x: nat)
  ensures
    exp_int(x, 1nat) == x,
{
    assert(exp_int(x, 1nat) == x * exp_int(x, 0nat));
    assert(exp_int(x, 0nat) == 1nat);
    assert(x * 1nat == x) by(nonlinear_arith);
}

/* helper modified by LLM (iteration 9): subrange/push relationship for sequence prefix extension */
proof fn lemma_subrange_push_eq<T>(s: Seq<T>, k: int)
  requires
    0 <= k < s.len(),
  ensures
    s.subrange(0int, k + 1) == s.subrange(0int, k).push(s[k]),
{
    assert(s.subrange(0int, k + 1) == s.subrange(0int, k).push(s[k]));
}

/* helper modified by LLM (iteration 9): subrange full-length equals sequence */
proof fn lemma_subrange_full<T>(s: Seq<T>)
  ensures
    s.subrange(0int, s.len()) == s,
{
    assert(s.subrange(0int, s.len()) == s);
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): fix int casts in proof by introducing int lengths; keep exponentiation-by-bits and Vec build */
  let len_usize: usize = sy.len();
  let len_i: int = sy@.len();

  let mut i: usize = 0usize;
  let mut acc: Seq<char> = seq!['1'];

  proof {
      assert(str2int(acc) == 1nat);
      assert(exp_int(str2int(sx@), 0nat) == 1nat);
      assert(str2int(acc) == exp_int(str2int(sx@), 0nat));
  }

  while i < len_usize
      invariant
          0int <= i as int <= len_i,
          valid_bit_string(sx@),
          valid_bit_string(sy@),
          valid_bit_string(acc),
          str2int(acc) == exp_int(str2int(sx@), str2int(sy@.subrange(0int, i as int))),
      decreases (len_i) - (i as int)
  {
      let sq = mul(acc, acc);
      proof {
          let p: nat = str2int(sy@.subrange(0int, i as int));
          lemma_exp_add(str2int(sx@), p, p);
          assert(str2int(sq) == exp_int(str2int(sx@), p + p));
      }
      let bit = sy[i];
      if bit == '1' {
          let acc2 = mul(sq, sx@);
          proof {
              let p: nat = str2int(sy@.subrange(0int, i as int));
              lemma_exp_add(str2int(sx@), p + p, 1nat);
              lemma_exp_one(str2int(sx@));
              let s = sy@.subrange(0int, (i as int) + 1);
              lemma_str2int_snoc(s);
              assert(s.len() > 0);
              assert(s.len() - 1 == i as int) by(nonlinear_arith);
              assert(s[s.len() - 1] == sy@[i as int]);
              assert(bit == sy@[i as int]);
              let p: nat = str2int(sy@.subrange(0int, i as int));
              assert(str2int(s) == 2nat * p + 1nat);
              assert((p + p) + 1nat == 2nat * p + 1nat) by(nonlinear_arith);
              assert(str2int(acc2) == exp_int(str2int(sx@), str2int(s)));
          }
          acc = acc2;
      } else {
          proof {
              let p: nat = str2int(sy@.subrange(0int, i as int));
              let s = sy@.subrange(0int, (i as int) + 1);
              lemma_str2int_snoc(s);
              assert(s.len() > 0);
              assert(s.len() - 1 == i as int) by(nonlinear_arith);
              assert(s[s.len() - 1] == sy@[i as int]);
              assert(bit == sy@[i as int]);
              assert(bit != '1');
              assert((if s[s.len() - 1] == '1' { 1nat } else { 0nat }) == 0nat);
              assert(str2int(s) == 2nat * p);
              assert(p + p == 2nat * p) by(nonlinear_arith);
              assert(str2int(sq) == exp_int(str2int(sx@), str2int(s)));
          }
          acc = sq;
      }
      i = i + 1usize;
  }
  proof {
      assert(i as int == len_i);
      assert(sy@.subrange(0int, len_i) == sy@);
  }

  let dm = div_mod(acc, sz@);
  let r = dm.1;

  let r_len: usize = r.len() as usize;
  let r_len_i: int = r.len();
  let mut res_vec: Vec<char> = Vec::new();
  let mut k: usize = 0usize;
  while k < r_len
      invariant
          0int <= k as int <= r_len_i,
          res_vec@ == r.subrange(0int, k as int),
      decreases (r_len_i) - (k as int)
  {
      let ch = r[k as int];
      res_vec.push(ch);
      proof {
          assert(k as int < r_len_i);
          lemma_subrange_push_eq(r, k as int);
          assert(res_vec@ == r.subrange(0int, (k as int) + 1));
      }
      k = k + 1usize;
  }
  proof {
      assert(k as int == r_len_i);
      assert(r.subrange(0int, r_len_i) == r);
  }

  res_vec
}
// </vc-code>


}

fn main() {}