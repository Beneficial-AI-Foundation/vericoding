// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
      valid_bit_string(dividend) && valid_bit_string(divisor),
      str2int(divisor) > 0,
  ensures 
      valid_bit_string(res.0) && valid_bit_string(res.1),
      str2int(res.0) == str2int(dividend) / str2int(divisor),
      str2int(res.1) == str2int(dividend) % str2int(divisor),
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
spec fn bit_to_nat(c: char) -> nat {
    if c == '1' { 1nat } else { 0nat }
}

/* helper modified by LLM (iteration 10): Fixed helpers remain unchanged */
proof fn lemma_str2int_zero(s: Seq<char>)
    requires
        valid_bit_string(s),
        all_zero(s),
    ensures
        str2int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_zero(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_exp_zero(x: nat)
    ensures
        exp_int(x, 0) == 1,
{
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires
        z > 0,
        y > 0,
    ensures
        exp_int(x % z, y) % z == exp_int(x, y) % z,
    decreases y
{
    if y == 1 {
        assert(exp_int(x % z, 1) % z == (x % z) % z == x % z == exp_int(x, 1) % z);
    } else {
        lemma_exp_mod(x, (y - 1) as nat, z);
        assert(exp_int(x % z, y) == (x % z) * exp_int(x % z, (y - 1) as nat));
        assert(exp_int(x % z, y) % z == ((x % z) * exp_int(x % z, (y - 1) as nat)) % z);
        assert(((x % z) * exp_int(x % z, (y - 1) as nat)) % z == ((x % z) * (exp_int(x % z, (y - 1) as nat) % z)) % z);
        assert(((x % z) * (exp_int(x % z, (y - 1) as nat) % z)) % z == ((x % z) * (exp_int(x, (y - 1) as nat) % z)) % z);
        assert(((x % z) * (exp_int(x, (y - 1) as nat) % z)) % z == (x * exp_int(x, (y - 1) as nat)) % z);
        assert((x * exp_int(x, (y - 1) as nat)) % z == exp_int(x, y) % z);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
      sy.len() > 0 && str2int(sz@) > 1,
  ensures 
      valid_bit_string(res@),
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type issues - use 0nat for comparison, store Vec lengths as usize, properly convert Seq to Vec */
    if sy.len() == 0 || str2int(sy@) == 0nat {
        proof {
            lemma_exp_zero(str2int(sx@));
        }
        let one = vec!['1'];
        proof {
            assert(str2int(one@) == 1) by {
                assert(one@.len() == 1);
                assert(one@[0] == '1');
                assert(str2int(one@) == 2 * str2int(one@.subrange(0, 0)) + 1);
                assert(one@.subrange(0, 0).len() == 0);
                assert(str2int(one@.subrange(0, 0)) == 0);
            }
        }
        let (_, remainder) = div_mod(one@, sz@);
        let mut res_vec = Vec::new();
        let mut i: usize = 0;
        let remainder_len: usize = remainder.len() as usize;
        while i < remainder_len
            invariant
                0 <= i <= remainder_len,
                remainder_len == remainder.len(),
                res_vec@.len() == i as int,
                forall|j: int| 0 <= j < i ==> res_vec@[j] == remainder[j],
        {
            res_vec.push(remainder[i as int]);
            i = i + 1;
        }
        proof {
            assert(res_vec@ =~= remainder);
            assert(str2int(res_vec@) == str2int(remainder));
            assert(str2int(remainder) == 1 % str2int(sz@));
            assert(exp_int(str2int(sx@), 0) == 1);
        }
        return res_vec;
    } else {
        let last_bit = sy[sy.len() - 1];
        let mut sy_div_2 = Vec::new();
        let mut i: usize = 0;
        while i < sy.len() - 1
            invariant
                0 <= i <= sy.len() - 1,
                sy_div_2@.len() == i as int,
                forall|j: int| 0 <= j < i ==> sy_div_2@[j] == sy@[j],
        {
            sy_div_2.push(sy[i]);
            i = i + 1;
        }
        
        proof {
            assert(sy_div_2@ =~= sy@.subrange(0, sy@.len() - 1));
            assert(str2int(sy@) == 2 * str2int(sy_div_2@) + bit_to_nat(last_bit));
        }
        
        let half_result = mod_exp(sx.clone(), sy_div_2, sz.clone());
        let (_, x_mod) = div_mod(sx@, sz@);
        
        if last_bit == '0' {
            let squared = div_mod(half_result@, sz@);
            let doubled = div_mod(squared.0, sz@);
            proof {
                assert(str2int(sy@) == 2 * str2int(sy@.subrange(0, sy@.len() - 1)));
                lemma_exp_mod(str2int(sx@), str2int(sy@.subrange(0, sy@.len() - 1)), str2int(sz@));
            }
            let mut res_vec = Vec::new();
            let mut j: usize = 0;
            let doubled_len: usize = doubled.1.len() as usize;
            while j < doubled_len
                invariant
                    0 <= j <= doubled_len,
                    doubled_len == doubled.1.len(),
                    res_vec@.len() == j as int,
                    forall|k: int| 0 <= k < j ==> res_vec@[k] == doubled.1[k],
            {
                res_vec.push(doubled.1[j as int]);
                j = j + 1;
            }
            return res_vec;
        } else {
            let squared = div_mod(half_result@, sz@);
            let doubled = div_mod(squared.0, sz@);
            let multiplied = div_mod(doubled.0, sz@);
            proof {
                assert(str2int(sy@) == 2 * str2int(sy@.subrange(0, sy@.len() - 1)) + 1);
                lemma_exp_mod(str2int(sx@), str2int(sy@.subrange(0, sy@.len() - 1)), str2int(sz@));
            }
            let mut res_vec = Vec::new();
            let mut j: usize = 0;
            let multiplied_len: usize = multiplied.1.len() as usize;
            while j < multiplied_len
                invariant
                    0 <= j <= multiplied_len,
                    multiplied_len == multiplied.1.len(),
                    res_vec@.len() == j as int,
                    forall|k: int| 0 <= k < j ==> res_vec@[k] == multiplied.1[k],
            {
                res_vec.push(multiplied.1[j as int]);
                j = j + 1;
            }
            return res_vec;
        }
    }
}
// </vc-code>


}

fn main() {}