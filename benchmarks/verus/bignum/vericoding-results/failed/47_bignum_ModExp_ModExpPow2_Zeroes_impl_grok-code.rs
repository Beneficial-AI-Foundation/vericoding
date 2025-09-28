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
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): changed to exec types, fixed compilation errors for Seq to Vec */
fn str2int_local(s: &Vec<char>) -> u128
{
    let mut result = 0u128;
    let mut i = 0usize;
    while i < s.len()
        invariant
            true,
        decreases s.len() - i
    {
        result = result * 2u128 + if s[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }
    result
}

fn mod_multiply(a: &Vec<char>, b: &Vec<char>, z: &Vec<char>) -> Vec<char>
  ensures
    valid_bit_string(mod_multiply(a, b, z)@),
    str2int(mod_multiply(a, b, z)@) == (str2int(a@) * str2int(b@)) % str2int(z@)
{
    let a_int = str2int_local(a);
    let b_int = str2int_local(b);
    let z_int = str2int_local(z);
    let m = (a_int * b_int) % z_int;
    if m == 0u128 {
        vec!['0']
    } else {
        let mut temp_res = Vec::new();
        let mut temp = m;
        while temp > 0u128
            invariant
                true,
            decreases temp
        {
            let bit = if (temp % 2u128) == 1u128 { '1' } else { '0' };
            temp_res.push(bit);
            temp /= 2u128;
        }
        temp_res.reverse();
        temp_res
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): implemented modular exponentiation, used Vec<char> */
{
    let mut res = vec!['1'];
    let mut current = sx.clone();
    let mut i: isize = (sy.len() as isize) - 1;
    while i >= 0
        invariant
            0 <= i && i <= sy.len() as int - 1 || i == -1,
            valid_bit_string(res@),
            valid_bit_string(current@),
            str2int(res@) == exp_int(str2int(sx@), str2int(sy@.subrange(0int, sy.len() as int - (i + 1)))) % str2int(sz@),
            str2int(current@) == exp_int(str2int(sx@), exp_int(2nat, i as nat)) % str2int(sz@)
        decreases 0 - i
    {
        if sy[i as usize] == '1' {
            res = mod_multiply(&res, &current, &sz);
        }
        current = mod_multiply(&current, &current, &sz);
        i -= 1;
    }
    res
}
// </vc-code>


}

fn main() {}