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
fn nat_to_binary_vec(n: u32) -> (res: Vec<char>)
    ensures res@ == nat_to_binary_string(n as nat),
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut res = nat_to_binary_vec(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        res.push(digit);
        res
    }
}

/* helper modified by LLM (iteration 2): fixed compilation error by changing `lemma fn` to `proof fn` */
proof fn lemma_nat_to_binary_string_is_valid(n: nat)
    ensures is_valid_binary(nat_to_binary_string(n)),
    decreases n
{
    if n > 0 {
        lemma_nat_to_binary_string_is_valid(n / 2);
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
    /* code modified by LLM (iteration 2): no changes; fixed compilation error in helper function */
    match width {
        None => {
            if num >= 0 {
                let n = num as u32;
                proof {
                    lemma_nat_to_binary_string_is_valid(n as nat);
                }
                nat_to_binary_vec(n)
            } else {
                let mut result = Vec::new();
                result.push('-');
                let n = if num == i32::MIN { 0x8000_0000u32 } else { (-num) as u32 };
                let mut binary_part = nat_to_binary_vec(n);
                proof {
                    lemma_nat_to_binary_string_is_valid(n as nat);
                }
                result.append(&mut binary_part);
                result
            }
        }
        Some(w) => {
            let val = num as u32;
            let mut result = Vec::with_capacity(w);
            let mut i: usize = 0;
            while i < w
                invariant
                    i <= w,
                    result.len() == i,
                    forall|j: int| 0 <= j < i ==> result@[j] == '0' || result@[j] == '1',
                decreases w - i
            {
                let bit_pos = w - 1 - i;
                let bit = if bit_pos >= 32 {
                    if num < 0 { 1u32 } else { 0u32 }
                } else {
                    (val >> (bit_pos as u32)) & 1
                };

                if bit == 1 {
                    result.push('1');
                } else {
                    result.push('0');
                }
                i = i + 1;
            }
            result
        }
    }
}
// </vc-code>

}
fn main() {}