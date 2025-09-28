// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor),
        str2int(divisor) > 0
    ensures 
        valid_bit_string(ret.0) && valid_bit_string(ret.1),
        str2int(ret.0) == str2int(dividend) / str2int(divisor),
        str2int(ret.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
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
/* helper modified by LLM (iteration 10): Fixed type errors with nat/usize conversions and Seq indexing */
fn bit_at(s: &Vec<char>, i: usize) -> (bit: char)
    requires
        i < s@.len(),
        valid_bit_string(s@)
    ensures
        bit == s@[i as int],
        bit == '0' || bit == '1'
{
    s[i]
}

fn is_zero_vec(s: &Vec<char>) -> (b: bool)
    requires
        valid_bit_string(s@)
    ensures
        b == all_zero(s@),
        b == (str2int(s@) == 0)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] == '0'
    {
        if s[i] != '0' {
            return false;
        }
        i = i + 1;
    }
    true
}

fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    requires
        valid_bit_string(s)
    ensures
        v@ == s,
        valid_bit_string(v@)
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    let ghost len_nat = s.len();
    while i < len_nat
        invariant
            0 <= i <= len_nat,
            i as int <= s.len(),
            v@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> v@[j] == s[j]
    {
        let ghost idx = i as int;
        proof {
            assert(idx < s.len());
        }
        let c: char = if s.index(idx) == '1' { '1' } else { '0' };
        v.push(c);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        sy@.len() > 0 && str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed integer literal type error in subrange call */
    if is_zero_vec(&sy) {
        let res_seq = zeros(1nat);
        return seq_to_vec(res_seq);
    }
    
    let sy_len = sy.len();
    if sy_len == 1 {
        if bit_at(&sy, 0) == '0' {
            let res_seq = zeros(1nat);
            return seq_to_vec(res_seq);
        } else {
            let (_, remainder) = div_mod(sx@, sz@);
            return seq_to_vec(remainder);
        }
    }
    
    let last_bit = bit_at(&sy, sy_len - 1);
    let ghost sy_div_2_len = (sy_len - 1) as int;
    let sy_div_2_seq = sy@.subrange(0, sy_div_2_len);
    let mut sy_div_2 = Vec::new();
    let mut i: usize = 0;
    while i < sy_len - 1
        invariant
            0 <= i <= sy_len - 1,
            sy_div_2@.len() == i,
            forall|j: int| 0 <= j < i ==> sy_div_2@[j] == sy@[j]
    {
        sy_div_2.push(sy[i]);
        i = i + 1;
    }
    
    assert(sy_div_2@ == sy_div_2_seq);
    
    let half_exp = mod_exp(sx, sy_div_2, sz.clone());
    let squared_seq = div_mod(half_exp@.add(half_exp@), sz@).1;
    let squared = seq_to_vec(squared_seq);
    
    if last_bit == '1' {
        let result_seq = div_mod(squared@.add(sx@), sz@).1;
        seq_to_vec(result_seq)
    } else {
        squared
    }
}
// </vc-code>


}

fn main() {}