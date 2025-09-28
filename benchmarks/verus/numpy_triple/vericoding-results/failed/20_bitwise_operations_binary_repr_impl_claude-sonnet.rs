// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nat_to_binary_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let digit = if n % 2 == 0 { '0' } else { '1' };
        nat_to_binary_string(n / 2).push(digit)
    }
}

spec fn is_valid_binary(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1')
}

spec fn is_valid_signed_binary(s: Seq<char>) -> bool {
    if s.len() > 0 && s[0] == '-' {
        is_valid_binary(s.skip(1))
    } else {
        is_valid_binary(s)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat literal comparisons and operations */
fn nat_to_binary_impl(n: nat) -> (result: Vec<char>)
    ensures
        result@ == nat_to_binary_string(n),
        is_valid_binary(result@)
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = nat_to_binary_impl(n / 2nat);
        let digit = if n % 2nat == 0nat { '0' } else { '1' };
        result.push(digit);
        result
    }
}

fn pad_to_width(binary: Vec<char>, width: usize) -> (result: Vec<char>)
    requires
        width >= 1,
        is_valid_binary(binary@)
    ensures
        result.len() == width,
        is_valid_binary(result@)
{
    let mut result = Vec::new();
    let pad_len = if binary.len() < width { width - binary.len() } else { 0 };
    
    for i in 0..pad_len
        invariant
            result.len() == i,
            is_valid_binary(result@)
    {
        result.push('0');
    }
    
    let copy_len = if binary.len() > width { width } else { binary.len() };
    let start_idx = if binary.len() > width { binary.len() - width } else { 0 };
    
    for i in start_idx..start_idx + copy_len
        invariant
            result.len() == pad_len + (i - start_idx),
            is_valid_binary(result@)
    {
        result.push(binary[i]);
    }
    
    result
}

fn nat_to_binary_exec(n: u32) -> (result: Vec<char>)
    ensures
        is_valid_binary(result@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = nat_to_binary_exec(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        result.push(digit);
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_repr(num: i32, width: Option<usize>) -> (result: Vec<char>)
    requires 
        width.is_some() ==> width.get_Some_0() >= 1,
    ensures 

        width.is_none() ==> is_valid_signed_binary(result@),
        width.is_some() ==> is_valid_binary(result@),

        width.is_some() ==> result.len() == width.get_Some_0(),

        (num >= 0 && width.is_none()) ==> 
            result@ == nat_to_binary_string(num as nat),

        (num < 0 && width.is_none()) ==> 
            result@.len() > 0 && result@[0] == '-' && is_valid_binary(result@.skip(1)),

        (num < 0 && width.is_some()) ==> {
            let w = width.get_Some_0();
            let two_comp = (1u32 << w) as i32 + num;
            two_comp >= 0 && two_comp < (1i32 << w) && result.len() == w
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced deprecated get_Some_0 with arrow operator */
    match width {
        None => {
            if num >= 0 {
                nat_to_binary_exec(num as u32)
            } else {
                let mut result = vec!['-'];
                let pos_binary = nat_to_binary_exec((-num) as u32);
                result.extend_from_slice(&pos_binary);
                result
            }
        }
        Some(w) => {
            if num >= 0 {
                let binary = nat_to_binary_exec(num as u32);
                pad_to_width(binary, w)
            } else {
                let two_comp = (1u32 << w) as i32 + num;
                let binary = nat_to_binary_exec(two_comp as u32);
                pad_to_width(binary, w)
            }
        }
    }
}
// </vc-code>

}
fn main() {}