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
/* helper modified by LLM (iteration 4): safe conversions between Vec<char> and usize with loop invariants */
fn vec_to_usize(s: &Vec<char>) -> usize {
    let mut r: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            // after processing i bits, r <= 2^i - 1
            r <= if i == 0 { 0usize } else { (1usize << i) - 1 },
        decreases s.len() - i
    {
        if s[i] == '1' {
            r = r * 2 + 1;
        } else {
            r = r * 2;
        }
        i = i + 1;
    }
    r
}

/* helper modified by LLM (iteration 4): convert usize to bit-vector of fixed length */
fn usize_to_bits(len: usize, mut v: usize) -> Vec<char> {
    let mut res: Vec<char> = Vec::new();
    if len == 0 {
        return res;
    }
    // compute pow = 2^(len-1)
    let mut pow: usize = 1;
    let mut k: usize = 1;
    while k < len
        invariant
            k <= len,
            // pow == 2^(k-1)
            pow == (1usize << (k - 1)),
        decreases len - k
    {
        pow = pow * 2;
        k = k + 1;
    }
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            // pow is the current highest power: pow == 2^(len - j - 1) when j < len
            (j < len) ==> (pow == (1usize << (len - j - 1))),
        decreases len - j
    {
        if v >= pow {
            res.push('1');
            v = v - pow;
        } else {
            res.push('0');
        }
        // safe: pow > 0 while j+1 < len
        if pow > 0 { pow = pow / 2; }
        j = j + 1;
    }
    res
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
    /* code modified by LLM (iteration 4): modular exponentiation using helper converters */
    // compute modulus m from sz
    let m: usize = vec_to_usize(&sz);
    // if modulus is 0 or 1 we handle as degenerate but spec requires str2int(sz@) > 1
    // perform a small runtime guard to avoid division-by-zero; this keeps executable safe
    if m <= 1 {
        // return a zero-vector of the correct length
        return usize_to_bits(sz.len(), 0);
    }
    // compute base value from sx modulo m
    let mut base: usize = vec_to_usize(&sx) % m;
    let mut res_nat: usize = 1 % m;
    let mut i: usize = 0;
    while i < sy.len()
        invariant
            i <= sy.len(),
        decreases sy.len() - i
    {
        let idx = sy.len() - 1 - i;
        if sy[idx] == '1' {
            res_nat = (res_nat * base) % m;
        }
        base = (base * base) % m;
        i = i + 1;
    }
    // convert result to bit-vector of length sz.len()
    let res_vec = usize_to_bits(sz.len(), res_nat);
    res_vec
}

// </vc-code>


}

fn main() {}