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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fix ghost type usage in function specifications and implementation */
fn bit_to_u8(c: char) -> u8 {
    if c == '1' { 1 } else { 0 }
}

fn vec_to_u64(v: Vec<char>) -> u64 {
    requires(valid_bit_string(v@));
    ensures(|result: u64| ghost {
        let result_nat: nat = result as nat;
        result_nat == str2int(v@)
    });
    {
        let mut result: u64 = 0;
        let mut i: usize = 0;
        
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                ghost {
                    let result_nat: nat = result as nat;
                    result_nat == str2int(v@.subrange(0, i))
                },
                valid_bit_string(v@.subrange(0, i))
            decreases v.len() - i
        {
            result = result * 2 + (bit_to_u8(v[i]) as u64);
            i = i + 1;
        }
        result
    }
}

fn u64_to_vec(mut n: u64, len: usize) -> Vec<char> {
    requires(n < (1u64 << len));
    ensures(valid_bit_string(result@) && ghost { str2int(result@) == n as nat });
    {
        let mut result = Vec::new();
        let mut i: usize = 0;
        
        while i < len
            invariant
                0 <= i <= len,
                result.len() == i,
                valid_bit_string(result@),
                ghost { str2int(result@) == n % (1u64 << i) as nat }
            decreases len - i
        {
            let bit = if n % 2 == 1 { '1' } else { '0' };
            result.push(bit);
            n = n / 2;
            i = i + 1;
        }
        result.reverse();
        result
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
/* code modified by LLM (iteration 10): Fix ghost type usage and variable scoping */
{
    let x = vec_to_u64(sx);
    let y = vec_to_u64(sy);
    let z_u64 = vec_to_u64(sz);
    
    proof {
        let z_nat: nat = z_u64 as nat;
        let x_nat: nat = x as nat;
        let y_nat: nat = y as nat;
    }
    
    let mut result_val: u64 = 1;
    let mut base = x % z_u64;
    let mut exp = y;
    
    while exp > 0
        invariant
            ghost {
                let result_nat: nat = result_val as nat;
                let base_nat: nat = base as nat;
                let exp_nat: nat = exp as nat;
                let z_nat: nat = z_u64 as nat;
                let x_nat: nat = x as nat;
                let y_nat: nat = y as nat;
                
                result_nat * exp_int(base_nat, exp_nat) % z_nat == exp_int(x_nat, y_nat) % z_nat,
                base < z_u64,
                exp <= y
            }
        decreases exp
    {
        if exp % 2 == 1 {
            result_val = (result_val * base) % z_u64;
        }
        base = (base * base) % z_u64;
        exp = exp / 2;
    }
    
    let len = sz.len();
    u64_to_vec(result_val, len)
}
// </vc-code>


}

fn main() {}