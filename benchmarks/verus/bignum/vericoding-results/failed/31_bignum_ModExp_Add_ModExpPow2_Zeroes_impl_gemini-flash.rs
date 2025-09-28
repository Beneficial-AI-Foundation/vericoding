// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
      0nat 
  } else { 
      2nat * str2int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
      valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
      valid_bit_string(res),
      str2int(res) == str2int(s1) + str2int(s2),
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
/* helper modified by LLM (iteration 10): Removed `use vstd::calc;` and fixed the helper functions so they are pure spec functions `spec fn`. The other part of the helper (int2str) is not needed for the mod_exp problem. */
spec fn int2str_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        int2str_spec(n / 2) + seq![if n % 2 == 1 { '1' } else { '0' }]
    }
}

spec fn int2str(n: nat) -> (s: Seq<char>)
    ensures
        s == int2str_spec(n),
        valid_bit_string(s),
        str2int(s) == n,
{
    if n == 0 {
        seq!['0']
    } else {
        let mut result = Seq::<char>::new();
        let mut temp_n = n;
        while temp_n > 0
            invariant
                valid_bit_string(result),
                temp_n >= 0,
            decreases temp_n
        {
            let digit = if temp_n % 2 == 1 { '1' } else { '0' };
            result = seq![digit] + result;
            temp_n = temp_n / 2;
        }
        result
    }
}

proof fn lemma_mult_mod_dist(a: nat, b: nat, m: nat)
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
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
/* code modified by LLM (iteration 10): The code was failing compilation because int and nat types cannot be used as a parameter to index a Seq<char> (sy[k_minus_1 as int]). Replaced int with usize and updated the conditional logic. */
{
  let sx_val = str2int(sx);
  let sy_val = str2int(sy);
  let sz_val = str2int(sz);

  let s_len = sy.len();

  if s_len == 1 {
      if sy[0] == '0' {
          return int2str(1);
      } else {
          return int2str(sx_val % sz_val);
      }
  }

  let k_minus_1: usize = (sy.len() - 1) as usize;

  let sy_prime = sy.subrange(0, k_minus_1 as int);
  let sy_last_bit = (sy[k_minus_1] == '1');

  let rec_res_seq = mod_exp(sx, sy_prime, sz);
  let rec_res_val = str2int(rec_res_seq);

  // y = 2y' + b_k-1
  assert(sy_val == 2 * str2int(sy_prime) + (if sy_last_bit { 1 } else { 0 }));

  assert(exp_int(sx_val, sy_val) % sz_val
      == exp_int(sx_val, 2 * str2int(sy_prime) + (if sy_last_bit { 1 } else { 0 })) % sz_val
  );

  let p2_res = rec_res_val * rec_res_val;

  proof {
    lemma_mult_mod_dist(rec_res_val, rec_res_val, sz_val);
    assert( (rec_res_val * rec_res_val) % sz_val == ( (rec_res_val % sz_val) * (rec_res_val % sz_val) ) % sz_val );
    assert(rec_res_val % sz_val == rec_res_val);
  }

  let p2_res_mod = p2_res % sz_val;

  if sy_last_bit {
      // x^(2y' + 1) = x^(2y') * x^1 (mod n)
      //               = (x^y')^2 * x (mod n)
      proof {
        lemma_mult_mod_dist(p2_res_mod, sx_val, sz_val);
      }
      let final_val = (p2_res_mod * sx_val) % sz_val;
      return int2str(final_val);
  } else {
      // x^(2y') = (x^y')^2 (mod n)
      return int2str(p2_res_mod);
  }
}
// </vc-code>


}

fn main() {}