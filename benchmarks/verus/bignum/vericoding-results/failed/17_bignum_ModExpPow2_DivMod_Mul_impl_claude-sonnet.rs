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
/* helper modified by LLM (iteration 10): Fixed type mismatches with proper nat literals and sequence indexing */
fn int2str(n: nat) -> (res: Seq<char>)
    ensures 
        valid_bit_string(res),
        str2int(res) == n,
    decreases n
{
    if n == 0nat {
        seq!['0']
    } else {
        let quotient = n / 2nat;
        let remainder = n % 2nat;
        let rest = int2str(quotient);
        if remainder == 0nat {
            rest.push('0')
        } else {
            rest.push('1')
        }
    }
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures 
        res@ == s
{
    let mut v = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j],
    {
        v.push(s[i]);
        i = i + 1;
    }
    v
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
    /* code modified by LLM (iteration 10): Fixed type mismatches with proper nat literals */
    if n == 0 {
        return seq_to_vec(seq!['1']);
    }
    
    let mut result = seq_to_vec(seq!['1']);
    let mut base = sx.clone();
    let mut exp = sy.clone();
    
    while str2int(exp@) > 0nat
        invariant
            valid_bit_string(result@),
            valid_bit_string(base@),
            valid_bit_string(exp@),
            str2int(result@) * exp_int(str2int(base@), str2int(exp@)) % str2int(sz@) == 
                exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
        decreases str2int(exp@)
    {
        let (new_exp, remainder) = div_mod(exp@, seq!['1', '0']);
        if str2int(remainder) == 1nat {
            let product = mul(result@, base@);
            let (_, new_result) = div_mod(product, sz@);
            result = seq_to_vec(new_result);
        }
        let square = mul(base@, base@);
        let (_, new_base) = div_mod(square, sz@);
        base = seq_to_vec(new_base);
        exp = seq_to_vec(new_exp);
    }
    
    result
}
// </vc-code>


}

fn main() {}