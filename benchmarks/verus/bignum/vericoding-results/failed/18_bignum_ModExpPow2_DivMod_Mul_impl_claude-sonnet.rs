// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if !valid_bit_string(s) {
        0nat
    } else if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed seq indexing and int literal types */
fn int2str_helper(n: u64) -> (res: Vec<char>)
    ensures valid_bit_string(res@)
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant temp <= n
            decreases temp
        {
            if temp % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / 2;
        }
        // Reverse the result
        let mut reversed = Vec::new();
        let mut i = result.len();
        while i > 0
            invariant i <= result.len()
            decreases i
        {
            i = i - 1;
            reversed.push(result[i]);
        }
        reversed
    }
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j],
        decreases s.len() - i
    {
        v.push(s[i as int]);
        i = i + 1;
    }
    v
}

fn vec_to_seq(v: &Vec<char>) -> (res: Seq<char>)
    ensures res == v@
{
    v@
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed nat literal and type compatibility issues */
    if n == 0 {
        if str2int(sy@) == 0 {
            return seq_to_vec(seq!['1']);
        } else {
            return seq_to_vec(seq!['1']);
        }
    }
    
    if sy[n as usize] == '0' {
        let mut new_sy = Vec::new();
        let mut i: usize = 0;
        while i < n as usize
            invariant
                0 <= i <= n,
                new_sy@.len() == i,
                forall|j: int| 0 <= j < i ==> new_sy@[j] == sy@[j],
            decreases n as int - i as int
        {
            new_sy.push(sy[i]);
            i = i + 1;
        }
        return mod_exp_pow2(sx, new_sy, (n - 1) as u8, sz);
    } else {
        let mut new_sy = Vec::new();
        let mut i: usize = 0;
        while i < n as usize
            invariant
                0 <= i <= n,
                new_sy@.len() == i,
                forall|j: int| 0 <= j < i ==> new_sy@[j] == sy@[j],
            decreases n as int - i as int
        {
            new_sy.push(sy[i]);
            i = i + 1;
        }
        
        let half_result = mod_exp_pow2(sx.clone(), new_sy, (n - 1) as u8, sz.clone());
        let squared = mul(half_result@, half_result@);
        let (_, remainder1) = div_mod(squared, sz@);
        let multiplied = mul(remainder1, sx@);
        let (_, final_remainder) = div_mod(multiplied, sz@);
        return seq_to_vec(final_remainder);
    }
}
// </vc-code>


}

fn main() {}