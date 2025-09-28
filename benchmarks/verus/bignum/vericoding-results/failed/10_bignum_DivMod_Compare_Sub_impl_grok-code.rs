// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
        str2int(s1) >= str2int(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) - str2int(s2),
{
    assume(false);
    unreached()
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        str2int(s1) < str2int(s2) ==> res == -1,
        str2int(s1) == str2int(s2) ==> res == 0,
        str2int(s1) > str2int(s2) ==> res == 1,
    decreases str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): implemented manual reverse to avoid Vec::reverse compilation error */
fn subtract_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(s1@) && valid_bit_string(s2@),
        str2int(s1@) >= str2int(s2@),
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) - str2int(s2@),
{
    let mut tmp = Vec::new();
    let mut max_len = s1.len();
    if s2.len() > max_len {
        max_len = s2.len();
    }
    let mut borrow = false;
    let mut i: usize = 0;
    while i < max_len
        invariant 
            borrow ==> str2int(s1@.subrange(0, s1@.len() - (i as int))) + (if borrow {1nat} else {0nat}) >= str2int(s2@.subrange(0, s2@.len() - (i as int))),
            i <= max_len,
    {
        let pos1 = if i < s1.len() { s1[s1.len() - 1 - i] } else { '0' };
        let pos2 = if i < s2.len() { s2[s2.len() - 1 - i] } else { '0' };
        let bit1 = (pos1 as u8 - '0' as u8) as i32;
        let bit2 = (pos2 as u8 - '0' as u8) as i32;
        let borrow_val = if borrow { 1i32 } else { 0i32 };
        let diff = bit1 - bit2 - borrow_val;
        let new_bit: u8;
        if diff < 0 {
            new_bit = (diff + 2) as u8;
            borrow = true;
        } else {
            new_bit = diff as u8;
            borrow = false;
        }
        let char_to_push = if new_bit == 0 { '0' } else { '1' };
        tmp.push(char_to_push);
        i += 1;
    }
    let mut result = Vec::new();
    let len_tmp = tmp.len();
    for j in 0..len_tmp {
        result.push(tmp[len_tmp - 1 - j]);
    }
    result
}

/* helper modified by LLM (iteration 10): implemented manual reverse to avoid Vec::reverse compilation error */
fn add_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@),
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) + str2int(s2@),
{
    let mut tmp = Vec::new();
    let mut max_len = s1.len();
    if s2.len() > max_len {
        max_len = s2.len();
    }
    let mut carry = false;
    let mut i: usize = 0;
    while i < max_len
        invariant 
            i <= max_len,
    {
        let pos1 = if i < s1.len() { s1[s1.len() - 1 - i] } else { '0' };
        let pos2 = if i < s2.len() { s2[s2.len() - 1 - i] } else { '0' };
        let bit1 = (pos1 as u8 - '0' as u8) as u32;
        let bit2 = (pos2 as u8 - '0' as u8) as u32;
        let carry_val = if carry { 1u32 } else { 0u32 };
        let sum = bit1 + bit2 + carry_val;
        let new_bit = (sum % 2) as u8;
        carry = sum >= 2;
        let char_to_push = if new_bit == 0 { '0' } else { '1' };
        tmp.push(char_to_push);
        i += 1;
    }
    if carry {
        tmp.push('1');
    }
    let mut result = Vec::new();
    let len_tmp = tmp.len();
    for j in 0..len_tmp {
        result.push(tmp[len_tmp - 1 - j]);
    }
    result
}

/* helper modified by LLM (iteration 10): fixed compare logic and syntax */
fn compare_bit_strings(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
    requires valid_bit_string(s1@) && valid_bit_string(s2@),
    ensures 
        str2int(s1@) < str2int(s2@) ==> res == -1,
        str2int(s1@) == str2int(s2@) ==> res == 0,
        str2int(s1@) > str2int(s2@) ==> res == 1,
{
    if s1.len() < s2.len() {
        return -1;
    } else if s1.len() > s2.len() {
        return 1;
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                0 <= (i as int) <= s1@.len(),
                forall|j: int| 0 <= j < (i as int) ==> s1@[j] == s2@[j],
        {
            if s1[i] < s2[i] {
                return -1;
            }
            if s1[i] > s2[i] {
                return 1;
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
    requires 
        valid_bit_string(dividend@) && valid_bit_string(divisor@),
        str2int(divisor@) > 0,
    ensures 
        valid_bit_string(res.0@) && valid_bit_string(res.1@),
        str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
        str2int(res.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed to make one mutable */
    let mut quot = Vec::new();
    let mut rem = dividend;
    while self::compare_bit_strings(rem.clone(), divisor.clone()) >= 0 {
        rem = self::subtract_bit_strings(rem, divisor.clone());
        let mut one = Vec::new();
        one.push('1');
        quot = self::add_bit_strings(quot, one);
    }
    (quot, rem)
}
// </vc-code>


}

fn main() {}