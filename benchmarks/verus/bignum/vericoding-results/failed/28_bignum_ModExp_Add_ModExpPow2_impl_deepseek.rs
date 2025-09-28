// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == 49u8 { 1nat } else { 0nat })
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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed duplicate exec function and fixed proof/exec function ambiguity */
proof fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  if str2int(sy) == 0 {
    proof {
      assert(exp_int(str2int(sx), 0) == 1nat);
      assert(1nat % str2int(sz) == 1nat);
    }
    Seq::from_vec(vec!['1'])
  } else {
    let mut res = sx.clone();
    let mut i: nat = 0;
    while i < n
      invariant
        i <= n,
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), exp_int(2nat, i)) % str2int(sz)
      decreases n - i
    {
      res = add(res.clone(), res);
      i = i + 1;
    }
    proof {
      assert(i == n);
      assert(exp_int(2nat, n) == str2int(sy));
      assert(str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz));
    }
    res
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed ghost type handling in executable code */
{
    if sy.len() == 0 {
        proof { assert(exp_int(str2int(sx@), 0) == 1nat); }
        return vec!['1'];
    }
    
    let n_val = sy.len() - 1;
    
    let pow2_seq = proof {
        let mut seq = Seq::new('0', sy.len());
        seq = seq.update(sy.len() - 1, '1');
        seq
    };
    
    let exponential = proof {
        mod_exp_pow2(sx@, pow2_seq, n_val as nat, sz@)
    };
    
    let result = if sy[0] == '1' {
        add(exponential.clone(), exponential)@
    } else {
        exponential
    };
    
    result.to_vec()
}
// </vc-code>


}

fn main() {}