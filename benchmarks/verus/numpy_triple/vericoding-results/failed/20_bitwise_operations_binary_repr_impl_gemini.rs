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
fn nat_to_binary_vec(n: u32) -> (result: Vec<char>)
    ensures
        result@ == nat_to_binary_string(n as nat),
        is_valid_binary(result@),
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut higher_bits = nat_to_binary_vec(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        higher_bits.push(digit);
        higher_bits
    }
}

/* helper modified by LLM (iteration 3): Removed precondition w<=32 by handling sign extension for w>32. */
fn int_to_binary_vec_fixed_width(num: i32, w: usize) -> (result: Vec<char>)
    requires
        1 <= w,
    ensures
        result.len() == w,
        is_valid_binary(result@),
{
    let mut result = Vec::with_capacity(w);
    let mut i: usize = 0;
    while i < w
        invariant
            0 <= i <= w,
            result.len() == i,
            (forall|j: int| 0 <= j < i ==> result@[j] == '0' || result@[j] == '1'),
        decreases w - i
    {
        let bit_idx = w - 1 - i;
        let bit_char = if bit_idx >= 32 {
            if num < 0 { '1' } else { '0' }
        } else {
            let bit = (num >> (bit_idx as u32)) & 1;
            if bit == 1 { '1' } else { '0' }
        };
        result.push(bit_char);
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 3): Replaced unsupported num.abs() with spec-compatible logic. */
    if let Some(w) = width {
        int_to_binary_vec_fixed_width(num, w)
    } else {
        if num >= 0 {
            nat_to_binary_vec(num as u32)
        } else {
            let abs_val_u32 = if num == i32::MIN {
                (1u32 << 31)
            } else {
                (-num) as u32
            };
            let mut binary_val = nat_to_binary_vec(abs_val_u32);
            
            let mut result = Vec::new();
            result.push('-');
            result.append(&mut binary_val);
            result
        }
    }
}
// </vc-code>

}
fn main() {}