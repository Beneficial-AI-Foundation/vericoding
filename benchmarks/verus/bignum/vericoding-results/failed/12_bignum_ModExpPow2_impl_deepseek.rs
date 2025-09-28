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
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type conversions and added spec function */
proof fn lemma_pow2_suffix_lower_bound(s: Seq<char>)
    requires 
        valid_bit_string(s),
        s.len() > 0,
    ensures 
        str2int(s) >= exp_int(2nat, (s.len() - 1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0' || s[0] == '1');
        if s[0] == '0' {
            assert(str2int(s) == 0nat);
            assert(exp_int(2nat, 0nat) == 1nat);
            assert(0nat >= 1nat);
        } else {
            assert(str2int(s) == 1nat);
            assert(1nat >= 1nat);
        }
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        lemma_pow2_suffix_lower_bound(prefix);
        assert(str2int(s) == 2nat * str2int(prefix) + (if s[s.len() - 1] == '1' {1nat} else {0nat}));
        assert(str2int(prefix) >= exp_int(2nat, (prefix.len() - 1) as nat));
        assert(exp_int(2nat, (s.len() - 1) as nat) == 2nat * exp_int(2nat, (prefix.len() - 1) as nat));
        assert(str2int(s) >= 2nat * exp_int(2nat, (prefix.len() - 1) as nat));
        assert(2nat * exp_int(2nat, (prefix.len() - 1) as nat) == exp_int(2nat, (s.len() - 1) as nat));
    }
}

spec fn spec_nat_to_usize(n: nat) -> usize
{
    n as usize
}

spec fn spec_usize_to_nat(u: usize) -> nat
{
    u as nat
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
/* code modified by LLM (iteration 10): Fixed type conversion mismatches and number representations */
{
    if n == 0 {
        let mut result = Vec::new();
        proof {
            let sy_val = str2int(sy@);
            if sy_val == 0nat {
                result.push('1');
            } else {
                let remainder_nat = exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@);
                if remainder_nat == 0nat {
                    result.push('0');
                } else {
                    let mut temp: usize = 0;
                    proof {
                        temp = spec_nat_to_usize(remainder_nat);
                    }
                    let mut bits = Vec::new();
                    let mut current = temp;
                    while current > 0
                        invariant
                            current >= 0,
                            bits@.len() <= 64,
                            valid_bit_string(bits@),
                        decreases current
                    {
                        if current % 2 == 0 {
                            bits.push('0');
                        } else {
                            bits.push('1');
                        }
                        current = current / 2;
                    }
                    if bits.is_empty() {
                        bits.push('0');
                    }
                    bits.reverse();
                    result = bits;
                }
            }
        }
        proof {
            lemma_pow2_suffix_lower_bound(sz@);
        }
        assert(valid_bit_string(result@));
        result
    } else {
        let y_dec = (n - 1) as u8;
        let mut sy_dec = sy.clone();
        sy_dec.pop();
        let res_part = mod_exp_pow2(sx, sy_dec, y_dec, sz);
        let mut result = Vec::new();
        proof {
            if sy[0] == '0' {
                result = res_part;
            } else {
                let res_val: usize;
                let sz_val: usize;
                proof {
                    res_val = spec_nat_to_usize(str2int(res_part@));
                    sz_val = spec_nat_to_usize(str2int(sz@));
                }
                let product = res_val * res_val;
                let remainder_val = product % sz_val;
                if remainder_val == 0 {
                    result.push('0');
                } else {
                    let mut bits = Vec::new();
                    let mut current = remainder_val;
                    while current > 0
                        invariant
                            current >= 0,
                            bits@.len() <= 64,
                            valid_bit_string(bits@),
                        decreases current
                    {
                        if current % 2 == 0 {
                            bits.push('0');
                        } else {
                            bits.push('1');
                        }
                        current = current / 2;
                    }
                    if bits.is_empty() {
                        bits.push('0');
                    }
                    bits.reverse();
                    result = bits;
                }
            }
        }
        proof {
            lemma_pow2_suffix_lower_bound(sz@);
        }
        assert(valid_bit_string(result@));
        result
    }
}
// </vc-code>


}

fn main() {}