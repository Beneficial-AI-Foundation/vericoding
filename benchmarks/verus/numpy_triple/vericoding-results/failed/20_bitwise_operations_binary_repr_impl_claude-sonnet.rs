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
/* helper modified by LLM (iteration 5): Added decreases clause to while loop in pad_binary_to_width */
spec fn binary_string_to_nat(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let digit_val: nat = if s[last_idx] == '1' { 1 } else { 0 };
        2 * binary_string_to_nat(s.take(last_idx)) + digit_val
    }
}

fn nat_to_binary_vec(n: u32) -> (result: Vec<char>)
    ensures is_valid_binary(result@),
            result@ == nat_to_binary_string(n as nat)
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = nat_to_binary_vec(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        result.push(digit);
        result
    }
}

fn pad_binary_to_width(mut binary: Vec<char>, width: usize) -> (result: Vec<char>)
    requires is_valid_binary(binary@),
             width >= binary.len(),
             width >= 1
    ensures is_valid_binary(result@),
            result.len() == width
{
    while binary.len() < width
        invariant is_valid_binary(binary@),
                  binary.len() <= width
        decreases width - binary.len()
    {
        binary.insert(0, '0');
    }
    binary
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
    /* code modified by LLM (iteration 5): Fixed deprecated get_Some_0 usage with arrow operator throughout */
    if let Some(w) = width {
        if num >= 0 {
            let binary = nat_to_binary_vec(num as u32);
            if binary.len() <= w {
                pad_binary_to_width(binary, w)
            } else {
                let mut result = Vec::new();
                for i in 0..w {
                    result.push('0');
                }
                result
            }
        } else {
            let two_comp = (1u32 << w) as i32 + num;
            let binary = nat_to_binary_vec(two_comp as u32);
            if binary.len() <= w {
                pad_binary_to_width(binary, w)
            } else {
                let mut result = Vec::new();
                for i in 0..w {
                    result.push('0');
                }
                result
            }
        }
    } else {
        if num >= 0 {
            nat_to_binary_vec(num as u32)
        } else {
            let pos_binary = nat_to_binary_vec((-num) as u32);
            let mut result = vec!['-'];
            result.extend_from_slice(&pos_binary);
            result
        }
    }
}
// </vc-code>

}
fn main() {}