// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == 49u8 { 1nat } else { 0nat })
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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    (str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0) &&
    sy.len() == n + 1 &&
    str2int(sz) > 1
  ensures 
    valid_bit_string(res) &&
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix seq indexing compilation errors by using proper nat/int conversions */
proof fn lemma_bit_string_char_equivalence()
    ensures
        49u8 as char == '1',
        48u8 as char == '0'
{
}

proof fn lemma_str2int_empty()
    ensures str2int(seq![]) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures str2int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
    ensures str2int(seq!['1']) == 1
{
    assert(seq!['1'][0] == '1');
    assert('1' == 49u8);
}

proof fn lemma_exp_int_base_cases()
    ensures
        exp_int(0, 0) == 1,
        exp_int(1, 0) == 1,
        forall|x: nat| exp_int(x, 0) == 1,
        forall|x: nat| exp_int(x, 1) == x
{
}

proof fn lemma_mod_properties()
    ensures
        forall|a: nat, m: nat| m > 1 ==> a % m < m,
        forall|a: nat, m: nat| m > 0 ==> (a % m) % m == a % m
{
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures
        res@ == s,
        valid_bit_string(res@)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            result@ == s.subrange(0, i as int),
            valid_bit_string(result@)
    {
        result.push(s[i as int]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fix seq indexing and type conversion compilation errors */
    if sy.len() == 1 {
        if sy[0] == '0' {
            let mut result = Vec::new();
            result.push('1');
            proof {
                lemma_str2int_single_zero();
                lemma_exp_int_base_cases();
                assert(str2int(sy@) == 0);
                assert(exp_int(str2int(sx@), 0) == 1);
                assert(str2int(result@) == 1);
            }
            result
        } else {
            let mut result = sx.clone();
            proof {
                lemma_str2int_single_one();
                lemma_exp_int_base_cases();
                assert(str2int(sy@) == 1);
                assert(exp_int(str2int(sx@), 1) == str2int(sx@));
            }
            result
        }
    } else {
        let mut sy_half = Vec::new();
        let mut i: usize = 0;
        while i < sy.len() - 1
            invariant
                0 <= i <= sy.len() - 1,
                sy_half.len() == i,
                valid_bit_string(sy_half@),
                forall|j: int| 0 <= j < i ==> sy_half[j] == sy[j]
        {
            sy_half.push(sy[i]);
            i += 1;
        }
        
        let sx_squared = mod_exp(sx.clone(), sy_half.clone(), sz.clone());
        
        let mut result = sx_squared.clone();
        result
    }
}
// </vc-code>


}

fn main() {}