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
/* helper modified by LLM (iteration 5): convert nat/u128 to Vec<char> matching nat_to_binary_string */
fn vec_of_nat(n: u128) -> (v: Vec<char>)
    ensures
        v@ == nat_to_binary_string(n as nat),
    decreases n as nat
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else {
        let mut v = vec_of_nat(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        v.push(digit);
        v
    }
}

/* helper modified by LLM (iteration 5): build fixed-width binary string from unsigned using safe shifts (avoid shifting by >=128) */
fn vec_of_unsigned(u: u128, w: usize) -> (result: Vec<char>)
    requires
        1 <= w,
    ensures
        result.len() == w,
        is_valid_binary(result@),
{
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < w
        invariant
            i <= w,
            v.len() == i,
        decreases w - i
    {
        let k = w - 1 - i;
        // avoid shifting by >= 128: treat bits beyond 127 as 0
        let bit = if k < 128 { (u >> k) & 1u128 } else { 0u128 };
        if bit == 1u128 {
            v.push('1');
        } else {
            v.push('0');
        }
        i += 1;
    }
    v
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
/* code modified by LLM (iteration 5): implement binary_repr for optional width and signed numbers, using helpers and safe arithmetic */
{
    if width.is_none() {
        if num >= 0 {
            vec_of_nat(num as u128)
        } else {
            let mut res: Vec<char> = Vec::new();
            res.push('-');
            let abs_n: u128 = (-(num as i128)) as u128;
            let tail = vec_of_nat(abs_n);
            let mut i: usize = 0;
            while i < tail.len()
                invariant
                    i <= tail.len(),
                    res.len() == 1 + i,
                decreases tail.len() - i
            {
                res.push(tail[i]);
                i += 1;
            }
            res
        }
    } else {
        let w = match width { Some(x) => x, None => 0 };
        if num >= 0 {
            let u: u128 = num as u128;
            // compute mod 2^w for indices beyond u's bits when w < 128; safe even if w >= 128
            if w == 0 {
                Vec::new()
            } else {
                let u_mod = if w < 128 { u % (1u128 << w) } else { u };
                vec_of_unsigned(u_mod, w)
            }
        } else {
            // negative number: produce two's-complement representation truncated/extended to width w
            let abs_u: u128 = (-(num as i128)) as u128;
            if w == 0 {
                Vec::new()
            } else if w < 128 {
                let two_pow: u128 = 1u128 << w;
                // two's complement for negative value in w bits is two_pow - abs_u (mod 2^w)
                let u = two_pow - abs_u % two_pow;
                vec_of_unsigned(u, w)
            } else {
                // w >= 128: compute lower 128-bit two's complement and extend with '1' bits for sign extension
                let lower_u = (!abs_u) + 1u128;
                if w == 128 {
                    vec_of_unsigned(lower_u, 128)
                } else {
                    // w > 128: leading ones then lower 128 bits
                    let mut v: Vec<char> = Vec::new();
                    let mut i: usize = 0;
                    while i < w - 128
                        invariant
                            i <= w - 128,
                            v.len() == i,
                        decreases (w - 128) - i
                    {
                        v.push('1');
                        i += 1;
                    }
                    let lower = vec_of_unsigned(lower_u, 128);
                    let mut j: usize = 0;
                    while j < lower.len()
                        invariant
                            j <= lower.len(),
                            v.len() == (w - 128) + j,
                        decreases lower.len() - j
                    {
                        v.push(lower[j]);
                        j += 1;
                    }
                    v
                }
            }
        }
    }
}

// </vc-code>

}
fn main() {}