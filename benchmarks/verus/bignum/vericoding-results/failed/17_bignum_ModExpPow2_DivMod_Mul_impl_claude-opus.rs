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
proof fn lemma_exp_zero(x: nat)
    ensures exp_int(x, 0) == 1nat
{
}

proof fn lemma_exp_split(x: nat, y1: nat, y2: nat)
    ensures exp_int(x, y1 + y2) == exp_int(x, y1) * exp_int(x, y2)
    decreases y2
{
    if y2 == 0 {
        lemma_exp_zero(x);
        assert(exp_int(x, y1 + 0) == exp_int(x, y1) * 1nat);
    } else {
        lemma_exp_split(x, y1, (y2 - 1) as nat);
        assert(exp_int(x, y1 + y2) == x * exp_int(x, y1 + (y2 - 1) as nat));
        assert(exp_int(x, y1 + y2) == x * exp_int(x, y1) * exp_int(x, (y2 - 1) as nat));
        assert(exp_int(x, y2) == x * exp_int(x, (y2 - 1) as nat));
        assert(exp_int(x, y1 + y2) == exp_int(x, y1) * exp_int(x, y2));
    }
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires z > 1
    ensures exp_int(x % z, y) % z == exp_int(x, y) % z
    decreases y
{
    if y == 0 {
        lemma_exp_zero(x);
        lemma_exp_zero(x % z);
    } else {
        lemma_exp_mod(x, (y - 1) as nat, z);
        assert(exp_int(x % z, y) == (x % z) * exp_int(x % z, (y - 1) as nat));
        assert(exp_int(x % z, y) % z == ((x % z) * exp_int(x % z, (y - 1) as nat)) % z);
        assert(((x % z) * exp_int(x % z, (y - 1) as nat)) % z == ((x % z) * (exp_int(x % z, (y - 1) as nat) % z)) % z);
        assert(exp_int(x % z, (y - 1) as nat) % z == exp_int(x, (y - 1) as nat) % z);
        assert(((x % z) * (exp_int(x, (y - 1) as nat) % z)) % z == (x * exp_int(x, (y - 1) as nat)) % z);
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
    }
}

/* helper modified by LLM (iteration 2): Added helper to create Vec from Seq */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j]
    {
        v.push(s[i as int]);
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
    /* code modified by LLM (iteration 2): Fixed type errors and used helper function */
    if n == 0 {
        assert(str2int(sy@) == exp_int(2nat, 0nat) || str2int(sy@) == 0nat);
        if str2int(sy@) == 0nat {
            let res = vec!['1'];
            proof {
                lemma_exp_zero(str2int(sx@));
                assert(str2int(res@) == 1nat);
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
            }
            return res;
        } else {
            proof {
                lemma_exp_zero(2nat);
            }
            assert(exp_int(2nat, 0nat) == 1nat);
            assert(str2int(sy@) == 1nat);
            let (_, res) = div_mod(sx.clone()@, sz@);
            assert(str2int(res) == str2int(sx@) % str2int(sz@));
            assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
            assert(str2int(res) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
            return seq_to_vec(res);
        }
    } else {
        let n_minus_1 = (n - 1) as u8;
        let mut half_y = vec!['1'];
        let mut i = 0;
        while i < n_minus_1
            invariant
                0 <= i <= n_minus_1,
                half_y@.len() == i as int + 1,
                half_y@[0] == '1',
                forall|j: int| 1 <= j < half_y@.len() ==> half_y@[j] == '0'
        {
            half_y.push('0');
            i = i + 1;
        }
        assert(half_y@.len() == n_minus_1 as int + 1);
        assert(str2int(half_y@) == exp_int(2nat, n_minus_1 as nat));
        
        let temp1 = mod_exp_pow2(sx.clone(), half_y.clone(), n_minus_1, sz.clone());
        assert(str2int(temp1@) == exp_int(str2int(sx@), exp_int(2nat, n_minus_1 as nat)) % str2int(sz@));
        
        let temp2 = mul(temp1.clone()@, temp1@);
        assert(str2int(temp2) == str2int(temp1@) * str2int(temp1@));
        
        let (_, res) = div_mod(temp2, sz@);
        assert(str2int(res) == str2int(temp2) % str2int(sz@));
        
        proof {
            let x_val = str2int(sx@);
            let z_val = str2int(sz@);
            let exp_half = exp_int(2nat, n_minus_1 as nat);
            let exp_full = exp_int(2nat, n as nat);
            
            assert(exp_full == 2nat * exp_half);
            lemma_exp_split(x_val, exp_half, exp_half);
            assert(exp_int(x_val, exp_half + exp_half) == exp_int(x_val, exp_half) * exp_int(x_val, exp_half));
            assert(exp_half + exp_half == 2nat * exp_half);
            assert(exp_int(x_val, exp_full) == exp_int(x_val, exp_half) * exp_int(x_val, exp_half));
            
            lemma_exp_mod(x_val, exp_half, z_val);
            assert(exp_int(x_val % z_val, exp_half) % z_val == exp_int(x_val, exp_half) % z_val);
            
            assert(str2int(temp1@) == exp_int(x_val, exp_half) % z_val);
            assert(str2int(temp2) == (exp_int(x_val, exp_half) % z_val) * (exp_int(x_val, exp_half) % z_val));
            assert(str2int(res) == ((exp_int(x_val, exp_half) % z_val) * (exp_int(x_val, exp_half) % z_val)) % z_val);
            assert(((exp_int(x_val, exp_half) % z_val) * (exp_int(x_val, exp_half) % z_val)) % z_val == (exp_int(x_val, exp_half) * exp_int(x_val, exp_half)) % z_val);
            assert(str2int(res) == exp_int(x_val, exp_full) % z_val);
            assert(str2int(sy@) == exp_full);
        }
        
        return seq_to_vec(res);
    }
}
// </vc-code>


}

fn main() {}