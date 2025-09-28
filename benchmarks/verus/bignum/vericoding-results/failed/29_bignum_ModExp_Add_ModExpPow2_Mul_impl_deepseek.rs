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
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fix helper functions with proper executable implementation */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s
{
    let mut v = Vec::new();
    let len = s.len() as usize;
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            v@ == s.subrange(0, i as int)
        decreases len - i
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

fn get_char_at(s: &Vec<char>, i: usize) -> (c: char)
    requires
        0 <= i < s.len()
    ensures
        c == s[i]
{
    s[i]
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
/* code modified by LLM (iteration 10): Fix variable scope and ensure proper result handling */
{
    let y_vec = seq_to_vec(sy);
    let len = y_vec.len();
    let mut acc = seq!['1'];
    let mut x = sx;
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            valid_bit_string(acc),
            valid_bit_string(x),
            exp_int(str2int(sx), str2int(sy.subrange(0, i as int))) % str2int(sz) == str2int(acc) % str2int(sz)
        decreases len - i
    {
        let bit = get_char_at(&y_vec, i);
        acc = mul(acc, acc);
        if bit == '1' {
            acc = mul(acc, x);
        }
        acc = mod_exp_pow2(acc, seq!['0', '1'], 1, sz);
        i += 1;
    }
    
    acc
}
// </vc-code>


}

fn main() {}