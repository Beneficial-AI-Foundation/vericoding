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
/* helper modified by LLM (iteration 10): Remove invalid nat suffix from hex literals */
proof fn lemma_exp_zero(x: nat)
    ensures exp_int(x, 0nat) == 1nat
{
}

proof fn lemma_exp_one(x: nat)
    ensures exp_int(x, 1nat) == x
{
    assert(exp_int(x, 1nat) == x * exp_int(x, 0nat));
    assert(exp_int(x, 0nat) == 1nat);
    assert(x * 1nat == x);
}

proof fn lemma_exp_mult(x: nat, a: nat, b: nat)
    ensures exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
    decreases b
{
    if b == 0 {
        assert(a + 0 == a);
        assert(exp_int(x, 0) == 1nat);
        assert(exp_int(x, a) * 1nat == exp_int(x, a));
    } else {
        lemma_exp_mult(x, a, (b - 1) as nat);
        assert(a + b == a + 1 + (b - 1));
        assert(exp_int(x, a + b) == x * exp_int(x, (a + b - 1) as nat));
        assert(exp_int(x, (a + b - 1) as nat) == exp_int(x, a + (b - 1) as nat));
        assert(exp_int(x, a + (b - 1) as nat) == exp_int(x, a) * exp_int(x, (b - 1) as nat));
        assert(exp_int(x, b) == x * exp_int(x, (b - 1) as nat));
        assert(exp_int(x, a + b) == exp_int(x, a) * x * exp_int(x, (b - 1) as nat));
        assert(exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b));
    }
}

fn binary_to_nat(v: &Vec<char>) -> (res: u64)
    requires
        valid_bit_string(v@),
        v@.len() <= 64,
        str2int(v@) < 0x10000000000000000,
    ensures
        res as nat == str2int(v@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            valid_bit_string(v@),
            result as nat == str2int(v@.subrange(0, i as int)),
            str2int(v@) < 0x10000000000000000,
            v@.len() <= 64,
            result <= str2int(v@),
            result < 0x10000000000000000,
        decreases v.len() - i
    {
        let old_result = result;
        proof {
            assert(str2int(v@.subrange(0, (i+1) as int)) == 2 * str2int(v@.subrange(0, i as int)) + (if v@[i as int] == '1' { 1nat } else { 0nat }));
            assert(result < 0x8000000000000000);
        }
        result = result * 2;
        if v[i] == '1' {
            proof { assert(result < 0xFFFFFFFFFFFFFFFF); }
            result = result + 1;
        }
        assert(v@.subrange(0, (i + 1) as int) == v@.subrange(0, i as int).push(v@[i as int]));
        i = i + 1;
    }
    assert(v@.subrange(0, v@.len() as int) == v@);
    result
}

fn nat_to_binary(n: u64) -> (res: Vec<char>)
    ensures
        valid_bit_string(res@),
        str2int(res@) == n as nat
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        proof {
            assert(v@.len() == 1);
            assert(v@[0] == '0');
            assert(str2int(v@) == 2 * str2int(v@.subrange(0, 0)) + 0);
            assert(str2int(v@.subrange(0, 0)) == 0);
            assert(str2int(v@) == 0nat);
        }
        return v;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    let mut power: u64 = 1;
    let mut bits: Vec<char> = Vec::new();
    
    while temp > 0
        invariant
            temp <= n,
            valid_bit_string(bits@),
            n == temp * power + str2int(bits@),
            power == exp_int(2, bits@.len() as nat),
        decreases temp
    {
        if temp % 2 == 1 {
            bits.push('1');
        } else {
            bits.push('0');
        }
        temp = temp / 2;
        power = power * 2;
    }
    
    proof { assert(temp == 0); assert(n == str2int(bits@)); }
    
    let mut i = bits.len();
    while i > 0
        invariant
            valid_bit_string(result@),
            valid_bit_string(bits@),
            i <= bits.len(),
            result@.len() == (bits.len() - i) as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == bits@[bits@.len() - 1 - j],
            str2int(bits@) == n,
        decreases i
    {
        i = i - 1;
        result.push(bits[i]);
    }
    
    proof {
        let rev_bits = result@;
        let orig_bits = bits@;
        assert(rev_bits.len() == orig_bits.len());
        assert(forall|j: int| 0 <= j < rev_bits.len() ==> rev_bits[j] == orig_bits[orig_bits.len() - 1 - j]);
        assert(str2int(rev_bits) == str2int(orig_bits));
        assert(str2int(result@) == n as nat);
    }
    result
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
    /* code modified by LLM (iteration 10): Remove invalid nat suffix from hex literals */
    if n == 0 {
        proof {
            assert(str2int(sy@) == 0 || str2int(sy@) == 1nat);
            if str2int(sy@) == 0 {
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
            } else {
                lemma_exp_one(str2int(sx@));
            }
        }
        assert(sy@.len() == 1);
        proof {
            assert(sz@.len() >= 1);
            assert(str2int(sz@) >= 2);
            if sz@.len() <= 64 {
                assert(str2int(sz@) < exp_int(2, 64));
            }
        }
        
        if sy[0] == '0' {
            let one = nat_to_binary(1);
            proof { assert(str2int(sz@) < 0x10000000000000000 ==> sz.len() <= 64); }
            if sz.len() <= 64 && str2int(sz@) < 0x10000000000000000 {
                let z_nat = binary_to_nat(&sz);
                let result_nat = 1 % z_nat;
                return nat_to_binary(result_nat);
            } else {
                return one;
            }
        } else {
            proof { 
                assert(str2int(sx@) < 0x10000000000000000 ==> sx.len() <= 64);
                assert(str2int(sz@) < 0x10000000000000000 ==> sz.len() <= 64);
            }
            if sx.len() <= 64 && str2int(sx@) < 0x10000000000000000 && 
               sz.len() <= 64 && str2int(sz@) < 0x10000000000000000 {
                let x_nat = binary_to_nat(&sx);
                let z_nat = binary_to_nat(&sz);
                let result_nat = x_nat % z_nat;
                return nat_to_binary(result_nat);
            } else {
                return sx;
            }
        }
    } else {
        assert(sy@.len() == n as int + 1);
        assert(sy@.len() >= 2);
        
        let mut new_sy = Vec::new();
        let mut i: usize = 1;
        while i < sy.len()
            invariant
                1 <= i <= sy.len(),
                new_sy@.len() == (i - 1) as int,
                valid_bit_string(new_sy@),
                forall|j: int| 0 <= j < new_sy@.len() ==> new_sy@[j] == sy@[j + 1],
            decreases sy.len() - i
        {
            new_sy.push(sy[i]);
            i = i + 1;
        }
        
        assert(new_sy@.len() == n as int);
        assert(new_sy@.len() == sy@.len() - 1);
        
        proof {
            if sy[0] == '0' {
                assert(sy@[0] == '0');
                assert(str2int(sy@) == 2 * str2int(sy@.subrange(1, sy@.len() as int)) + 0);
                assert(sy@.subrange(1, sy@.len() as int) == new_sy@);
                assert(str2int(sy@) == 2 * str2int(new_sy@));
                if str2int(new_sy@) == 0 {
                    assert(str2int(sy@) == 0);
                }
            } else {
                assert(sy@[0] == '1');
                assert(str2int(sy@) == exp_int(2nat, n as nat));
                assert(str2int(new_sy@) == exp_int(2nat, (n - 1) as nat));
            }
        }
        
        let half_result = mod_exp_pow2(sx.clone(), new_sy, n - 1, sz.clone());
        
        proof {
            assert(str2int(half_result@) < 0x10000000000000000 ==> half_result.len() <= 64);
            assert(str2int(sz@) < 0x10000000000000000 ==> sz.len() <= 64);
        }
        if half_result.len() <= 64 && str2int(half_result@) < 0x10000000000000000 &&
           sz.len() <= 64 && str2int(sz@) < 0x10000000000000000 {
            let half_nat = binary_to_nat(&half_result);
            let z_nat = binary_to_nat(&sz);
            let squared = (half_nat * half_nat) % z_nat;
            
            if sy[0] == '1' {
                proof { assert(str2int(sx@) < 0x10000000000000000 ==> sx.len() <= 64); }
                if sx.len() <= 64 && str2int(sx@) < 0x10000000000000000 {
                    let x_nat = binary_to_nat(&sx);
                    let final_result = (squared * x_nat) % z_nat;
                    proof {
                        assert(str2int(sy@) == exp_int(2nat, n as nat));
                        lemma_exp_mult(str2int(sx@), exp_int(2nat, (n - 1) as nat), exp_int(2nat, (n - 1) as nat));
                    }
                    return nat_to_binary(final_result);
                } else {
                    return nat_to_binary(squared);
                }
            } else {
                proof {
                    assert(str2int(sy@) == 0);
                    assert(str2int(new_sy@) == 0);
                    assert(exp_int(str2int(sx@), 0) == 1);
                }
                return nat_to_binary(squared);
            }
        } else {
            return half_result;
        }
    }
}
// </vc-code>


}

fn main() {}