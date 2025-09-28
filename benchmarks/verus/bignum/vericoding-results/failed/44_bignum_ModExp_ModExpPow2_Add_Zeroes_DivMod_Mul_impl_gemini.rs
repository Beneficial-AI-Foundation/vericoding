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
/* helper modified by LLM (iteration 8): fix syntax error in forall proof block */
proof fn lemma_subrange_is_valid_bit_string(s: Seq<char>, i: int, j: int)
  requires
    valid_bit_string(s),
    0 <= i <= j <= s.len(),
  ensures
    valid_bit_string(s.subrange(i,j))
{
    let sub = s.subrange(i, j);
    forall|k: int| 0 <= k < sub.len()
        ensures sub[k] == '0' || sub[k] == '1'
    {
        let original_idx = i + k;
        assert(sub.spec_index(k) == s.spec_index(original_idx));
        assert(s[original_idx] == '0' || s[original_idx] == '1');
    }
}

proof fn lemma_exp_add(x: nat, y1: nat, y2: nat)
  ensures exp_int(x, y1 + y2) == exp_int(x, y1) * exp_int(x, y2)
  decreases y2
{
  if y2 > 0 {
    lemma_exp_add(x, y1, (y2 - 1) as nat);
    reveal_with_fuel(exp_int, 2);
    vstd::math::mul_is_associative(x as int, exp_int(x, y1) as int, exp_int(x, (y2 - 1) as nat) as int);
    vstd::math::mul_is_commutative(x as int, exp_int(x, y1) as int);
  }
}

proof fn lemma_exp_add1(base: nat, y: nat)
  ensures exp_int(base, y + 1) == exp_int(base, y) * base
{
  reveal_with_fuel(exp_int, 2);
  vstd::math::mul_is_commutative(base as int, exp_int(base, y) as int);
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
    /* code modified by LLM (iteration 8): fix compilation error */
    if sy.len() == 1 {
        if sy.index(0) == '0' {
            let res = seq!['1'];
            assert(valid_bit_string(res));
            assert(str2int(res) == 1);
            return res;
        } else {
            let (_, rem) = div_mod(sx, sz);
            return rem;
        }
    }

    let y_prefix = sy.subrange(0, sy.len() - 1);
    proof {
        lemma_subrange_is_valid_bit_string(sy, 0, sy.len() - 1);
    }

    let temp_res_s = mod_exp(sx, y_prefix, sz);
    let squared_s = mul(temp_res_s, temp_res_s);
    let (_, temp_mod) = div_mod(squared_s, sz);

    let x = str2int(sx);
    let z = str2int(sz);
    let y_prefix_val = str2int(y_prefix);

    proof {
        vstd::math::power2_mod_equivalence(exp_int(x, y_prefix_val) as int, z as int);
        lemma_exp_add(x, y_prefix_val, y_prefix_val);
    }
    
    if sy.last() == '0' {
        return temp_mod;
    } else {
        let (_, sx_mod_sz) = div_mod(sx, sz);
        let prod_s = mul(temp_mod, sx_mod_sz);
        let (_, res) = div_mod(prod_s, sz);

        proof {
            let exp_prefix_sq = exp_int(x, 2 * y_prefix_val);
            vstd::math::mod_mul_equality(exp_prefix_sq as int, x as int, z as int);
            lemma_exp_add1(x, 2 * y_prefix_val);
        }
        return res;
    }
}
// </vc-code>


}

fn main() {}