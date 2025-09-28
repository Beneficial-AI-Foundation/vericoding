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
fn nat_to_bin_vec(n: u64, w: usize) -> Vec<char>
{
    let mut res = Vec::with_capacity(w);
    let mut i: usize = 0;
    while i < w
    {
        let bit = ((n >> (w - 1 - i)) & 1) == 1;
        res.push(if bit { '1' } else { '0' });
        i = i + 1;
    }
    res
}

fn nat_to_unpadded_vec(n: u64) -> Vec<char>
{
    if n == 0 {
        return vec!['0'];
    }
    let mut x = n;
    let mut res = Vec::new();
    while x > 0 {
        res.push(if (x & 1) == 0 { '0' } else { '1' });
        x >>= 1;
    }
    res.reverse();
    res
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
    if width.is_none() {
        let num_u: u64 = if num >= 0 { (num as u32) as u64 } else { ((-num) as i32) as u32 as u64 ;
        if num_u == 0 {
            let mut res = Vec::new();
            res.push('0');
            res
        } else {
            let mut res = if num < 0 { vec!['-'] } else { Vec::new() };
            let bin = nat_to_unpadded_vec(num_u);
            res.extend(bin);
            res
        }
    } else {
        let w = width.get_Some_0();
        let mask: u64 = 1u64 << w;
        let unsigned_val: u64 = if num >= 0 {
            (num as u32) as u64 & (mask - 1)
        } else {
            mask + (num as i32 as u32 as u64)
        };
        nat_to_bin_vec(unsigned_val, w)
    }
}
// </vc-code>

}
fn main() {}