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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires
      valid_bit_string(dividend) && valid_bit_string(divisor) &&
      str2int(divisor) > 0
  ensures
      valid_bit_string(result.0) && valid_bit_string(result.1) &&
      str2int(result.0) == str2int(dividend) / str2int(divisor) &&
      str2int(result.1) == str2int(dividend) % str2int(divisor)
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
/* helper modified by LLM (iteration 10): Fixed type mismatches by using proper nat literals and casting */
spec fn is_power_of_2(n: nat) -> bool {
    exists|k: nat| n == exp_int(2nat, k)
}

spec fn log2_floor(n: nat) -> nat
    recommends n > 0
{
    if n == 1 { 0nat } else { 1nat + log2_floor(n / 2) }
}

proof fn lemma_power_of_2_structure(n: nat)
    requires n > 0 && is_power_of_2(n)
    ensures exists|k: nat| n == exp_int(2nat, k)
{
}

proof fn lemma_mod_exp_identity(x: nat, y: nat, z: nat)
    requires z > 1
    ensures exp_int(x, y) % z == exp_int(x % z, y) % z
{
}

proof fn lemma_exp_decomposition(x: nat, y: nat)
    ensures y > 0 ==> exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
{
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires
      valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
      sy.len() > 0 && str2int(sz) > 1
  ensures
      valid_bit_string(res) &&
      str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed compilation error by avoiding int cast in executable code */
    if str2int(sy) == 0nat {
        seq!['1']
    } else if str2int(sy) == 1nat {
        let (_, remainder) = div_mod(sx, sz);
        remainder
    } else {
        let sy_len = sy.len();
        let sy_half = sy.subrange(0, sy_len - 1);
        let recursive_result = mod_exp(sx, sy_half, sz);
        
        if is_power_of_2(str2int(sy)) {
            proof {
                let n: nat = log2_floor(str2int(sy));
            }
            mod_exp_pow2(sx, sy, log2_floor(str2int(sy)), sz)
        } else {
            let (quotient, remainder) = div_mod(sy, seq!['1', '0']);
            let even_part = mod_exp(sx, quotient, sz);
            let squared = mod_exp(even_part, seq!['1', '0'], sz);
            
            if str2int(remainder) == 1nat {
                let (_, sx_mod) = div_mod(sx, sz);
                add(squared, sx_mod)
            } else {
                squared
            }
        }
    }
}
// </vc-code>


}

fn main() {}