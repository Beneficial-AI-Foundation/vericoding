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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
     (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
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

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed Seq indexing and nat/usize type mismatches */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut result = Vec::new();
            result.push('1');
            proof {
                assert(sy@[0] == '0');
                assert(str2int(sy@) == 0nat);
                assert(exp_int(str2int(sx@), 0nat) == 1nat);
                assert(str2int(result@) == 1nat);
                assert(1nat % str2int(sz@) < str2int(sz@));
            }
            let (_, remainder) = div_mod(result@, sz@);
            let mut res_vec = Vec::new();
            let mut i: usize = 0;
            while i < remainder.len() as usize
                invariant
                    i <= remainder.len(),
                    res_vec@.len() == i as nat,
                    forall|j: int| 0 <= j < i ==> res_vec@[j] == remainder[j],
            {
                res_vec.push(remainder[i as int]);
                i = i + 1;
            }
            return res_vec;
        } else {
            let (_, remainder) = div_mod(sx@, sz@);
            let mut res_vec = Vec::new();
            let mut i: usize = 0;
            while i < remainder.len() as usize
                invariant
                    i <= remainder.len(),
                    res_vec@.len() == i as nat,
                    forall|j: int| 0 <= j < i ==> res_vec@[j] == remainder[j],
            {
                res_vec.push(remainder[i as int]);
                i = i + 1;
            }
            proof {
                assert(sy@[0] == '1');
                assert(str2int(sy@) == 1nat);
                assert(exp_int(str2int(sx@), 1nat) == str2int(sx@));
            }
            return res_vec;
        }
    }
    
    let last_bit = sy[sy.len() - 1];
    let mut sy_div2 = Vec::new();
    for i in 0..(sy.len() - 1)
        invariant
            sy_div2@.len() == i,
            forall|j: int| 0 <= j < i ==> sy_div2@[j] == sy@[j as int],
    {
        sy_div2.push(sy[i]);
    }
    
    if last_bit == '0' {
        proof {
            assert(sy@[sy@.len() - 1] == '0');
            assert(str2int(sy@) == 2nat * str2int(sy_div2@));
            assert(exp_int(str2int(sx@), str2int(sy@)) == exp_int(exp_int(str2int(sx@), 2nat), str2int(sy_div2@)));
        }
        let sx_squared = mul(sx@, sx@);
        let mut sx_squared_vec = Vec::new();
        let mut i: usize = 0;
        while i < sx_squared.len() as usize
            invariant
                i <= sx_squared.len(),
                sx_squared_vec@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> sx_squared_vec@[j] == sx_squared[j],
        {
            sx_squared_vec.push(sx_squared[i as int]);
            i = i + 1;
        }
        return mod_exp(sx_squared_vec, sy_div2, sz);
    } else {
        proof {
            assert(sy@[sy@.len() - 1] == '1');
            assert(str2int(sy@) == 2nat * str2int(sy_div2@) + 1nat);
            assert(exp_int(str2int(sx@), str2int(sy@)) == str2int(sx@) * exp_int(exp_int(str2int(sx@), 2nat), str2int(sy_div2@)));
        }
        let sx_squared = mul(sx@, sx@);
        let mut sx_squared_vec = Vec::new();
        let mut i: usize = 0;
        while i < sx_squared.len() as usize
            invariant
                i <= sx_squared.len(),
                sx_squared_vec@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> sx_squared_vec@[j] == sx_squared[j],
        {
            sx_squared_vec.push(sx_squared[i as int]);
            i = i + 1;
        }
        let temp = mod_exp(sx_squared_vec, sy_div2, sz);
        let product = mul(sx@, temp@);
        let (_, remainder) = div_mod(product, sz@);
        let mut res_vec = Vec::new();
        let mut i: usize = 0;
        while i < remainder.len() as usize
            invariant
                i <= remainder.len(),
                res_vec@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> res_vec@[j] == remainder[j],
        {
            res_vec.push(remainder[i as int]);
            i = i + 1;
        }
        return res_vec;
    }
}
// </vc-code>


}

fn main() {}