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
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) &&
        str2int(divisor) > 0,
    ensures 
        valid_bit_string(res.0) && valid_bit_string(res.1) &&
        str2int(res.0) == str2int(dividend) / str2int(divisor) &&
        str2int(res.1) == str2int(dividend) % str2int(divisor),
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed seq_to_vec by using executable conversion and indexing with usize */
proof fn lemma_exp_int_zero(x: nat)
    ensures exp_int(x, 0) == 1nat
{
}

proof fn lemma_exp_int_succ(x: nat, y: nat)
    ensures exp_int(x, y + 1) == x * exp_int(x, y)
{
}

proof fn lemma_mod_exp_base(x: nat, m: nat)
    requires m > 1
    ensures exp_int(x, 0nat) % m == 1nat % m
{
    assert(exp_int(x, 0nat) == 1nat);
}

proof fn lemma_mod_exp_square(x: nat, y: nat, m: nat)
    requires m > 1, y % 2 == 0, y > 0
    ensures exp_int(x, y) % m == exp_int(x * x % m, y / 2) % m
{
}

proof fn lemma_mod_exp_odd(x: nat, y: nat, m: nat)
    requires m > 1, y % 2 == 1, y > 0
    ensures exp_int(x, y) % m == (x % m * exp_int(x, (y - 1) as nat) % m) % m
{
}

fn zero_string() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2int(res@) == 0
{
    vec!['0']
}

fn one_string() -> (res: Vec<char>)
    ensures valid_bit_string(res@) && str2int(res@) == 1
{
    vec!['1']
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures valid_bit_string(res@) && res@ == s
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let len = s.len() as usize;
    while i < len
        invariant
            valid_bit_string(result@),
            result@.len() == i,
            result@ == s.subrange(0, i as int),
            i <= len,
            len == s.len()
    {
        result.push(s[i]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
        sy@.len() == n as int + 1 &&
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed compilation error by removing int cast for sequence indexing */
    if n == 0 {
        proof {
            lemma_exp_int_zero(str2int(sx@));
            lemma_mod_exp_base(str2int(sx@), str2int(sz@));
        }
        let one = one_string();
        let (_, remainder) = div_mod(one@, sz@);
        seq_to_vec(remainder)
    } else {
        let mut half_exp = sy.clone();
        half_exp[n as usize] = '0';
        
        let half_result = mod_exp_pow2(sx.clone(), half_exp, n - 1, sz.clone());
        let squared = mul(half_result@, half_result@);
        let (_, mod_squared) = div_mod(squared, sz@);
        
        if sy[n as usize] == '1' {
            let (_, x_mod) = div_mod(sx@, sz@);
            let final_mul = mul(mod_squared, x_mod);
            let (_, final_result) = div_mod(final_mul, sz@);
            seq_to_vec(final_result)
        } else {
            seq_to_vec(mod_squared)
        }
    }
}
// </vc-code>


}

fn main() {}