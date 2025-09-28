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
/* helper modified by LLM (iteration 4): No changes needed, helpers are correct */
spec fn exp_mod(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 0
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else {
        (base * exp_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn lemma_exp_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures exp_mod(base, exp, modulus) == exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        assert(exp_mod(base, 0, modulus) == 1nat % modulus);
        assert(exp_int(base, 0) == 1nat);
    } else {
        lemma_exp_mod_correct(base, (exp - 1) as nat, modulus);
        assert(exp_mod(base, exp, modulus) == (base * exp_mod(base, (exp - 1) as nat, modulus)) % modulus);
        assert(exp_int(base, exp) == base * exp_int(base, (exp - 1) as nat));
        assert((base * exp_mod(base, (exp - 1) as nat, modulus)) % modulus == (base * (exp_int(base, (exp - 1) as nat) % modulus)) % modulus);
        assert((base * (exp_int(base, (exp - 1) as nat) % modulus)) % modulus == (base * exp_int(base, (exp - 1) as nat)) % modulus);
    }
}

proof fn lemma_exp_int_pow2(n: nat)
    ensures exp_int(2, n) > 0
    decreases n
{
    if n == 0 {
        assert(exp_int(2, 0) == 1);
    } else {
        lemma_exp_int_pow2((n - 1) as nat);
        assert(exp_int(2, n) == 2 * exp_int(2, (n - 1) as nat));
    }
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
    /* code modified by LLM (iteration 4): Fixed indexing by using usize directly instead of casting to int */
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;
    
    if n == 0 {
        proof {
            assert(sy_seq.len() == 1);
            assert(str2int(sy_seq) == exp_int(2, 0) || str2int(sy_seq) == 0);
            if str2int(sy_seq) == 1 {
                assert(exp_int(str2int(sx_seq), 1) == str2int(sx_seq));
                lemma_exp_mod_correct(str2int(sx_seq), 1, str2int(sz_seq));
            } else {
                assert(str2int(sy_seq) == 0);
                assert(exp_int(str2int(sx_seq), 0) == 1);
                lemma_exp_mod_correct(str2int(sx_seq), 0, str2int(sz_seq));
            }
        }
        
        if str2int(sy_seq) == 0nat {
            let one = seq!['1'];
            proof {
                assert(valid_bit_string(one));
                assert(str2int(one) == 1);
            }
            let (_, r) = div_mod(one, sz_seq);
            let mut result = Vec::new();
            let mut i: usize = 0;
            while i < r.len()
                invariant
                    0 <= i <= r.len(),
                    result@.len() == i,
                    forall|j: int| 0 <= j < i ==> result@[j] == r[j],
            {
                result.push(r[i]);
                i = i + 1;
            }
            proof { assert(result@ == r); }
            return result;
        } else {
            let (_, r) = div_mod(sx_seq, sz_seq);
            let mut result = Vec::new();
            let mut i: usize = 0;
            while i < r.len()
                invariant
                    0 <= i <= r.len(),
                    result@.len() == i,
                    forall|j: int| 0 <= j < i ==> result@[j] == r[j],
            {
                result.push(r[i]);
                i = i + 1;
            }
            proof { assert(result@ == r); }
            return result;
        }
    } else {
        let sy_half_vec: Vec<char> = sy.iter().skip(1).cloned().collect();
        let sy_half = sy_half_vec@;
        
        proof {
            assert(sy_half == sy_seq.subrange(1, sy_seq.len() as int));
            assert(sy_half.len() == n as int);
            assert(forall|i: int| 0 <= i < sy_half.len() ==> sy_half[i] == sy_seq[i + 1]);
            assert(valid_bit_string(sy_half));
            
            if str2int(sy_seq) == exp_int(2, n as nat) {
                lemma_exp_int_pow2(n as nat);
                assert(str2int(sy_half) == exp_int(2, (n - 1) as nat));
            } else {
                assert(str2int(sy_seq) == 0);
                assert(str2int(sy_half) == 0);
            }
        }
        
        let r_half = mod_exp_pow2(sx.clone(), sy_half_vec, (n - 1) as u8, sz.clone());
        let r_half_squared = mul(r_half@, r_half@);
        let (_, res) = div_mod(r_half_squared, sz_seq);
        
        proof {
            if str2int(sy_seq) == 0 {
                assert(str2int(sy_half) == 0);
                assert(str2int(r_half@) == exp_int(str2int(sx_seq), 0) % str2int(sz_seq));
                assert(exp_int(str2int(sx_seq), 0) == 1);
                assert(str2int(res) == str2int(r_half_squared) % str2int(sz_seq));
                assert(str2int(r_half_squared) == str2int(r_half@) * str2int(r_half@));
            } else {
                assert(str2int(sy_seq) == exp_int(2, n as nat));
                assert(str2int(sy_half) == exp_int(2, (n - 1) as nat));
                assert(str2int(r_half@) == exp_int(str2int(sx_seq), str2int(sy_half)) % str2int(sz_seq));
                lemma_exp_mod_correct(str2int(sx_seq), str2int(sy_half), str2int(sz_seq));
                assert(str2int(r_half@) == exp_int(str2int(sx_seq), exp_int(2, (n - 1) as nat)) % str2int(sz_seq));
                assert(str2int(res) == (str2int(r_half@) * str2int(r_half@)) % str2int(sz_seq));
                assert(exp_int(str2int(sx_seq), exp_int(2, n as nat)) == exp_int(str2int(sx_seq), exp_int(2, (n - 1) as nat)) * exp_int(str2int(sx_seq), exp_int(2, (n - 1) as nat)));
            }
        }
        
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < res.len()
            invariant
                0 <= i <= res.len(),
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == res[j],
        {
            result.push(res[i]);
            i = i + 1;
        }
        proof { assert(result@ == res); }
        return result;
    }
}
// </vc-code>


}

fn main() {}