// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s.index(s.len() - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s.index(i) == '0' || s.index(i) == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): conversions between Vec<char> and u128, modular power, and associated correctness proofs */
fn vec_to_u128(s: &Vec<char>) -> u128 {
    let mut acc: u128 = 0u128;
    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == '1' {
            acc = acc * 2u128 + 1u128;
        } else {
            acc = acc * 2u128;
        }
        i += 1;
    }
    acc
}

proof fn vec_to_u128_correct(s: &Vec<char>) {
    proof {
        let mut i: usize = 0;
        let mut acc: u128 = 0u128;
        while i < s.len()
            invariant
                (acc as nat) == str2int(s@.subrange(0, i as int))
            decreases s.len() - i
        {
            if s[i] == '1' {
                acc = acc * 2u128 + 1u128;
            } else {
                acc = acc * 2u128;
            }
            i += 1;
        }
        assert((acc as nat) == str2int(s@));
    }
}

fn u128_to_vec(n: u128) -> Vec<char> {
    if n == 0u128 {
        Vec::new()
    } else {
        let mut prefix = u128_to_vec(n / 2u128);
        if n % 2u128 == 1u128 {
            prefix.push('1');
        } else {
            prefix.push('0');
        }
        prefix
    }
}

proof fn u128_to_vec_correct(n: u128) {
    proof {
        if n == 0u128 {
            // empty -> 0, trivial
        } else {
            u128_to_vec_correct(n / 2u128);
            let v = u128_to_vec(n);
            assert(str2int(v@) == 2nat * str2int(u128_to_vec(n / 2u128)@) + (if n % 2u128 == 1u128 { 1nat } else { 0nat }));
            assert(str2int(u128_to_vec(n / 2u128)@) == (n / 2u128) as nat);
            assert(str2int(v@) == n as nat);
        }
    }
}

fn pow_mod_u128(base: u128, exp: &Vec<char>, modulus: u128) -> u128 {
    let mut result: u128 = 1u128 % modulus;
    let mut i: usize = 0;
    while i < exp.len() {
        // process bits left-to-right (MSB-first as represented in the Vec)
        result = (result * result) % modulus;
        if exp[i] == '1' {
            result = (result * base) % modulus;
        }
        i += 1;
    }
    result
}

proof fn pow_mod_u128_correct(sx: &Vec<char>, sy: &Vec<char>, sz: &Vec<char>, base: u128, modulus: u128, res: u128)
    requires base == vec_to_u128(sx) && modulus == vec_to_u128(sz) && res == pow_mod_u128(base, sy, modulus)
{
    proof {
        vec_to_u128_correct(sx);
        vec_to_u128_correct(sy);
        vec_to_u128_correct(sz);
        let base_spec = str2int(sx@);
        let mod_spec = str2int(sz@);
        let mut i: usize = 0;
        let mut acc: u128 = 1u128 % modulus;
        while i < sy.len()
            invariant
                (acc as nat) == exp_int(base_spec, str2int(sy@.subrange(0, i as int))) % mod_spec
            decreases sy.len() - i
        {
            acc = (acc * acc) % modulus;
            if sy[i] == '1' {
                acc = (acc * base) % modulus;
            }
            i += 1;
        }
        assert((acc as nat) == exp_int(base_spec, str2int(sy@)) % mod_spec);
        assert((res as nat) == exp_int(base_spec, str2int(sy@)) % mod_spec);
    }
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
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): convert inputs to u128, compute modular exponentiation, and convert back */
  let base = vec_to_u128(&sx);
  let modulus = vec_to_u128(&sz);
  let res_u = pow_mod_u128(base, &sy, modulus);
  let res = u128_to_vec(res_u);
  proof {
    pow_mod_u128_correct(&sx, &sy, &sz, base, modulus, res_u);
    u128_to_vec_correct(res_u);
  }
  res
}

// </vc-code>


}

fn main() {}