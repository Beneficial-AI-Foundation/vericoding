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
/* helper modified by LLM (iteration 5): Replace deprecated get_Some_0 with pattern matching and add proper lemmas */
proof fn nat_to_binary_string_properties(n: nat) 
    ensures 
        nat_to_binary_string(n).len() > 0 && 
        (forall|i: int| 0 <= i < nat_to_binary_string(n).len() ==> nat_to_binary_string(n)[i] == '0' || nat_to_binary_string(n)[i] == '1') 
    decreases n 
{
    if n == 0 {
    } else {
        nat_to_binary_string_properties(n / 2);
    }
}

proof fn binary_repr_correctness_lemma(num: i32, w: usize)
    requires w >= 1
    ensures binary_repr(num, Some(w)).len() == w
{
}

spec fn option_unwrap<T>(opt: Option<T>) -> T {
    match opt {
        Some(x) => x,
        None => arbitrary(),
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
/* code modified by LLM (iteration 5): Fix compilation error by removing recursive call and implementing proper logic */
{
    match width {
        Some(w) => {
            assert(w >= 1);
            
            if num >= 0 {
                let mut result = Vec::new();
                let mut n = num as u32;
                
                for i in 0..w {
                    let bit_pos = w - 1 - i;
                    let bit = (n >> bit_pos) & 1;
                    result.push(if bit == 0 { '0' } else { '1' });
                }
                
                result
            } else {
                let twos_comp = (1u32 << w) as i32 + num;
                assert(twos_comp >= 0);
                assert(twos_comp < (1i32 << w));
                
                let mut result = Vec::new();
                let mut n = twos_comp as u32;
                
                for i in 0..w {
                    let bit_pos = w - 1 - i;
                    let bit = (n >> bit_pos) & 1;
                    result.push(if bit == 0 { '0' } else { '1' });
                }
                
                result
            }
        },
        None => {
            let mut result = Vec::new();
            
            if num >= 0 {
                let mut n = num as u32;
                
                if n == 0 {
                    result.push('0');
                } else {
                    while n > 0 {
                        let digit = if n % 2 == 0 { '0' } else { '1' };
                        result.push(digit);
                        n = n / 2;
                    }
                    let mut temp_vec = Vec::new();
                    let len = result.len();
                    for i in 0..len {
                        temp_vec.push(result[len - 1 - i]);
                    }
                    result = temp_vec;
                }
            } else {
                result.push('-');
                let positive_num = (-num) as u32;
                let mut temp_result = Vec::new();
                
                if positive_num == 0 {
                    temp_result.push('0');
                } else {
                    let mut n = positive_num;
                    while n > 0 {
                        let digit = if n % 2 == 0 { '0' } else { '1' };
                        temp_result.push(digit);
                        n = n / 2;
                    }
                    let mut reversed = Vec::new();
                    let len = temp_result.len();
                    for i in 0..len {
                        reversed.push(temp_result[len - 1 - i]);
                    }
                    temp_result = reversed;
                }
                
                for c in temp_result {
                    result.push(c);
                }
            }
            
            result
        }
    }
}
// </vc-code>

}
fn main() {}