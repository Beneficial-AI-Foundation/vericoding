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
/* helper modified by LLM (iteration 5): recursive nat to binary Vec<char> */
fn nat_to_binary_vec(n: u64) -> Vec<char> {
    decreases n;
    if n == 0u64 {
        let mut v = Vec::<char>::new();
        v.push('0');
        v
    } else {
        let digit = if n % 2u64 == 0u64 { '0' } else { '1' };
        let mut v = nat_to_binary_vec(n / 2u64);
        v.push(digit);
        v
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
    /* code modified by LLM (iteration 5): implement binary_repr for signed values and fixed width (two's complement) */
    if width.is_none() {
        if num >= 0 {
            let n_u: u64 = num as u64;
            nat_to_binary_vec(n_u)
        } else {
            let mag: u64 = ((-(num as i64)) as u64);
            let mut res = Vec::<char>::new();
            res.push('-');
            let digits = nat_to_binary_vec(mag);
            let mut i: usize = 0usize;
            while i < digits.len()
                invariant i <= digits.len();
                decreases digits.len() - i;
            {
                res.push(digits[i]);
                i += 1;
            }
            res
        }
    } else {
        let w = width.get_Some_0();
        let modulus: u128 = 1u128 << w;
        let val_i128: i128 = if num >= 0 { num as i128 } else { (modulus as i128) + (num as i128) };
        let val: u128 = val_i128 as u128;
        let mut res = Vec::<char>::with_capacity(w);
        let mut i: usize = 0usize;
        while i < w
            invariant i <= w;
            decreases w - i;
        {
            let pos = w - 1 - i;
            let bit = ((val >> pos) & 1u128) == 1u128;
            if bit { res.push('1'); } else { res.push('0'); }
            i += 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}