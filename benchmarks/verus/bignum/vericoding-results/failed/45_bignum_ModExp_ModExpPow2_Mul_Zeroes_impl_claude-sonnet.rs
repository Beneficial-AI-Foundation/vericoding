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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2)
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
/* helper modified by LLM (iteration 10): fixed seq_to_vec to use usize index directly */
proof fn lemma_exp_decomp(x: nat, y: nat)
    requires y > 0
    ensures exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(s) < exp_int(2nat, s.len())
    decreases s.len()
{
    if s.len() > 0 {
        lemma_str2int_bound(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_mod_properties(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_exp_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    requires valid_bit_string(s)
    ensures
        v@ == s,
        valid_bit_string(v@)
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            0 <= i <= s.len(),
            v@ == s.subrange(0, i as int),
            valid_bit_string(v@)
    {
        v.push(s[i]);
        i = i + 1;
    }
    v
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
{
    /* code modified by LLM (iteration 10): fixed seq_to_vec parameter passing and proper indexing */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let zero_result = zeros(1nat);
            seq_to_vec(zero_result)
        } else {
            let sx_seq = sx@;
            let sz_seq = sz@;
            let result_seq = mod_exp_pow2(sx_seq, sy@, 0nat, sz_seq);
            seq_to_vec(result_seq)
        }
    } else {
        let mut sy_half = sy.clone();
        sy_half.pop();
        
        let rec_result = mod_exp(sx.clone(), sy_half, sz.clone());
        let squared_seq = mul(rec_result@, rec_result@);
        seq_to_vec(squared_seq)
    }
}
// </vc-code>


}

fn main() {}