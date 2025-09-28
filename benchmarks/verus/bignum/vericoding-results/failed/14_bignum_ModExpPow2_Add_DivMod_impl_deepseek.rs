// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fix typo in function names and variable references */
proof fn div_mod_lemma(dividend: nat, divisor: nat) 
    requires divisor > 0
    ensures 
        dividend % divisor == (dividend % divisor) % divisor,
        dividend % divisor < divisor,
        dividend == divisor * (dividend / divisor) + dividend % divisor
{
}

proof fn exp_int_lemma(x: nat, y: nat)
    ensures 
        exp_int(x, y) == (if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }),
        (y == 0) ==> (exp_int(x, y) == 1nat),
        (y > 0) ==> (exp_int(x, y) == x * exp_int(x, (y - 1) as nat))
{
}

proof fn str2int_lemma(s: Seq<char>)
    requires valid_bit_string(s)
    ensures 
        str2int(s) == if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) },
        (s.len() == 0) ==> (str2int(s) == 0nat),
        (s.len() > 0) ==> (str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }))
{
}

proof fn exp_int_zero_lemma(x: nat, y: nat)
    requires y == 0
    ensures exp_int(x, y) == 1nat
{
}

proof fn exp_int_pow2_lemma(n: nat)
    ensures exp_int(2nat, n) == (1 << n) as nat
    decreases n
{
    if n > 0 {
        exp_int_pow2_lemma((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix variable name typo and function name typo in proof blocks */
{
    if n == 0 {
        proof {
            exp_int_zero_lemma(str2int(sx@), str2int(sy@));
            assert(exp_int(str2int(sx@), 0) == 1nat);
            assert(str2int(sy@) == 0 || str2int(sy@) == 1nat);
            div_mod_lemma(1nat, str2int(sz@));
        }
        if str2int(sy@) == 0 {
            let one_vec = vec!['1'];
            proof { 
                assert(valid_bit_string(one_vec@));
                assert(str2int(one_vec@) == 1nat);
                assert(1nat % str2int(sz@) == 1nat % str2int(sz@));
            }
            one_vec
        } else {
            let remainder_result = div_mod(sx@, sz@);
            let remainder = remainder_result.1;
            proof {
                assert(str2int(remainder) == str2int(sx@) % str2int(sz@));
                assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
                assert(str2int(sx@) % str2int(sz@) == exp_int(str2int(sx@), 1nat) % str2int(sz@));
            }
            let res_vec = Vec::new();
            let mut i: usize = 0;
            while i < remainder.len() 
                invariant
                    0 <= i <= remainder.len(),
                    res_vec@ == remainder.subrange(0, i)
            {
                res_vec.push(remainder[i]);
                i += 1;
            }
            res_vec
        }
    } else {
        let len = sy@.len();
        let last_idx = len - 1;
        let new_sy_seq = sy@.update(last_idx, '0');
        proof {
            assert(valid_bit_string(new_sy_seq));
            assert(str2int(new_sy_seq) == exp_int(2nat, (n - 1) as nat) || str2int(new_sy_seq) == 0);
            assert(new_sy_seq.len() == n as usize);
        }
        let new_sy_vec = Vec::new();
        let mut j: usize = 0;
        while j < new_sy_seq.len() 
            invariant
                0 <= j <= new_sy_seq.len(),
                new_sy_vec@ == new_sy_seq.subrange(0, j)
        {
            new_sy_vec.push(new_sy_seq[j]);
            j += 1;
        }
        let temp = mod_exp_pow2(sx, new_sy_vec, n - 1, sz);
        let temp_squared = add(temp@, temp@);
        proof {
            assert(str2int(temp_squared) == 2nat * str2int(temp@));
            assert(exp_int(str2int(sx@), str2int(new_sy_seq)) % str2int(sz@) == str极nt(temp@));
            assert(2nat * (exp_int(str2int(sx@), str2int(new_sy_seq)) % str2int(sz@)) == str2int(temp_squared));
        }
        if sy@[last_idx] == '1' {
            let temp_squared_mod_result = div_mod(temp_squared, sz@);
            let temp_squared_mod = temp_squared_mod_result.1;
            let result = add(temp_squared_mod, sx@);
            let result_mod_result = div_mod(result, sz@);
            let result_mod = result_mod_result.1;
            proof {
                assert(str2int(result_mod) == (2nat * (exp_int(str2int(sx@), str2int(new_sy_seq)) % str2int(sz@)) + str2int(sx@)) % str2int(sz@));
                assert(exp_int(str2int(sx@), str2int(sy@)) == str2int(sx@) * exp_int(str2int(sx@), str2int(new_sy_seq)));
            }
            let res_vec = Vec::new();
            let mut k: usize = 0;
            while k < result_mod.len() 
                invariant
                    0 <= k <= result_mod.len(),
                    res_vec@ == result_mod.subrange(0, k)
            {
                res_vec.push(result_mod[k]);
                k += 1;
            }
            res_vec
        } else {
            let result_mod_result = div_mod(temp_squared, sz@);
            let result_mod = result_mod_result.1;
            proof {
                assert(str2int(result_mod) == (2nat * (exp_int(str2int(sx@), str2int(new_sy_seq)) % str2int(sz@))) % str2int(sz@));
                assert(exp_int(str2int(sx@), str2int(sy@)) == exp_int(str2int(sx@), str2int(new_sy_seq)) * 2nat);
            }
            let res_vec = Vec::new();
            let mut k: usize = 0;
            while k < result_mod.len() 
                invariant
                    0 <= k <= result_mod.len(),
                    res_vec@ == result_mod.subrange(0, k)
            {
                res_vec.push(result_mod[k]);
                k += 1;
            }
            res_vec
        }
    }
}
// </vc-code>


}

fn main() {}