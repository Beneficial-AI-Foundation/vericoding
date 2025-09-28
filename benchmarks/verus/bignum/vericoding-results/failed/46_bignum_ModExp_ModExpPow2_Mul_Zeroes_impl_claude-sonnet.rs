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
/* helper modified by LLM (iteration 10): Convert sequence to vector without using int indexing */
fn seq_to_vec_helper(s: Seq<char>) -> (v: Vec<char>)
    requires valid_bit_string(s)
    ensures
        v@ == s,
        valid_bit_string(v@),
        str2int(v@) == str2int(s)
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    let s_len_usize = s.len() as usize;
    while i < s_len_usize
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            v@ == s.subrange(0, i as int),
            valid_bit_string(v@),
            s_len_usize == s.len()
        decreases s_len_usize - i
    {
        proof {
            assert(0 <= i < s.len());
        }
        v.push(s[i]);
        i += 1;
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
    /* code modified by LLM (iteration 10): Use usize for all vector indexing and avoid int for sequence indexing */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut result = Vec::new();
            result.push('1');
            return result;
        } else {
            let sx_seq = sx@;
            let sz_seq = sz@;
            let res_seq = mod_exp_pow2(sx_seq, sy@, 0nat, sz_seq);
            let mut result = Vec::new();
            let mut i: usize = 0;
            let res_len = res_seq.len() as usize;
            while i < res_len
                invariant
                    0 <= i <= res_seq.len(),
                    result@.len() == i,
                    result@ == res_seq.subrange(0, i as int),
                    valid_bit_string(result@),
                    res_len == res_seq.len()
                decreases res_len - i
            {
                result.push(res_seq[i]);
                i += 1;
            }
            return result;
        }
    }
    
    let mut sy_half = Vec::new();
    let mut i: usize = 0;
    let sy_half_len = sy.len() - 1;
    while i < sy_half_len
        invariant
            0 <= i <= sy.len() - 1,
            sy_half@.len() == i,
            sy_half@ == sy@.subrange(0, i as int),
            valid_bit_string(sy_half@),
            sy_half_len == sy.len() - 1
        decreases sy_half_len - i
    {
        sy_half.push(sy[i]);
        i += 1;
    }
    
    let temp_res = mod_exp(sx.clone(), sy_half, sz.clone());
    let squared = mul(temp_res@, temp_res@);
    
    let mut squared_vec = Vec::new();
    let mut j: usize = 0;
    let squared_len = squared.len() as usize;
    while j < squared_len
        invariant
            0 <= j <= squared.len(),
            squared_vec@.len() == j,
            squared_vec@ == squared.subrange(0, j as int),
            valid_bit_string(squared_vec@),
            squared_len == squared.len()
        decreases squared_len - j
    {
        squared_vec.push(squared[j]);
        j += 1;
    }
    
    if sy[sy.len() - 1] == '0' {
        return squared_vec;
    } else {
        let final_mul = mul(squared_vec@, sx@);
        let mut result = Vec::new();
        let mut k: usize = 0;
        let final_len = final_mul.len() as usize;
        while k < final_len
            invariant
                0 <= k <= final_mul.len(),
                result@.len() == k,
                result@ == final_mul.subrange(0, k as int),
                valid_bit_string(result@),
                final_len == final_mul.len()
            decreases final_len - k
        {
            result.push(final_mul[k]);
            k += 1;
        }
        return result;
    }
}
// </vc-code>


}

fn main() {}