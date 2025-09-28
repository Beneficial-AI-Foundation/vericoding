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
/* helper modified by LLM (iteration 10): Fixed quantifier syntax */
spec fn is_power_of_2(n: nat) -> bool {
    exists|k: nat| n == exp_int(2nat, k)
}

proof fn lemma_exp_split(x: nat, y1: nat, y2: nat, z: nat)
    requires z > 1
    ensures exp_int(x, y1 + y2) % z == (exp_int(x, y1) % z * exp_int(x, y2) % z) % z
    decreases y2
{
    if y2 == 0 {
        assert(exp_int(x, y2) == 1nat);
        assert(y1 + y2 == y1);
        assert(exp_int(x, y1 + y2) == exp_int(x, y1));
    } else {
        assert(exp_int(x, y1 + y2) == x * exp_int(x, if y1 + y2 >= 1 { ((y1 + y2) - 1) as nat } else { 0nat }));
        lemma_exp_split(x, y1, (y2 - 1) as nat, z);
    }
}

fn bit_string_zero() -> (res: Seq<char>)
    ensures
        valid_bit_string(res),
        str2int(res) == 0
{
    seq!['0']
}

fn bit_string_one() -> (res: Seq<char>)
    ensures
        valid_bit_string(res),
        str2int(res) == 1nat
{
    seq!['1']
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
    /* code modified by LLM (iteration 10): Fixed quantifier syntax in while loop invariant */
    if sy.len() == 1 && sy =~= seq!['0'] {
        return bit_string_one();
    }
    
    let n = (sy.len() - 1) as usize;
    let mut i: usize = n;
    let mut found = false;
    
    while i > 0
        invariant
            i <= n,
            !found ==> forall|j: int| (i as int < j && j <= n as int) ==> sy[j] == '0'
    {
        if sy[i as int] == '1' {
            found = true;
            break;
        }
        i = i - 1;
    }
    
    if !found && sy[0] == '0' {
        return bit_string_one();
    }
    
    if !found && sy[0] == '1' {
        proof {
            let n_ghost: nat = 0nat;
            assert(sy.len() == n_ghost + 1);
        }
        let ghost n_param: nat = 0nat;
        return mod_exp_pow2(sx, sy, n_param, sz);
    }
    
    let sy_high = sy.subrange(0 as int, (i + 1) as int);
    let sy_low = sy.subrange((i + 1) as int, sy.len() as int);
    
    proof {
        assert(str2int(sy_high) > 0);
        assert(valid_bit_string(sy_high));
        assert(valid_bit_string(sy_low));
        assert(forall|j: int| 0 <= j < sy_low.len() ==> sy_low[j] == '0');
    }
    
    let res_high = mod_exp(sx, sy_high, sz);
    let ghost n_val: nat = (sy_low.len() - 1) as nat;
    proof {
        assert(sy_low.len() == n_val + 1);
    }
    let res_low = mod_exp_pow2(res_high, sy_low, n_val, sz);
    
    proof {
        lemma_exp_split(str2int(sx), str2int(sy_high), str2int(sy_low), str2int(sz));
    }
    
    res_low
}
// </vc-code>


}

fn main() {}