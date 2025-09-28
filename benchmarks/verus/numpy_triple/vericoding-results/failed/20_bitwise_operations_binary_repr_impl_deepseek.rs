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


proof fn lemma_div_mod(a: nat, b: nat)
    requires
        b > 0,
    ensures
        a / b * b + a % b == a,
        a % b < b,
{
}

proof fn lemma_pow2_positive(w: nat)
    ensures
        (1u32 << w) > 0,
{
}

fn abs(num: i32) -> (result: u32)
    ensures
        if num >= 0 { result == num as u32 } else { result == (-num) as u32 },
{
    if num >= 0 {
        num as u32
    } else {
        (-num) as u32
    }
}

fn build_binary_string(n: u32) -> (result: Vec<char>)
    ensures
        result@ == nat_to_binary_string(n as nat),
        is_valid_binary(result@),
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut remaining = n;
        
        while remaining > 0
            invariant
                remaining >= 0,
                is_valid_binary(digits@),
                digits@ == nat_to_binary_string(remaining as nat).drop_last(),
        {
            let digit = if remaining % 2 == 0 { '0' } else { '1' };
            digits.push(digit);
            remaining = remaining / 2;
        }
        
        let mut reversed = Vec::new();
        let mut i = digits.len();
        
        while i > 0
            invariant
                i <= digits.len(),
                is_valid_binary(reversed@),
                reversed@ == digits@.subrange(0, i).reverse(),
        {
            i = i - 1;
            reversed.push(digits[i]);
        }
        
        reversed
    }
}

/* helper modified by LLM (iteration 5): Replaced reverse() call with manual reversal to avoid mutable reference error */

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
    /* code modified by LLM (iteration 5): Fixed deprecated get_Some_0() calls with destructuring */
    if let Some(w) = width {
        proof { lemma_pow2_positive(w as nat); }
        
        let modulus = 1u32 << w;
        let abs_num = abs(num);
        
        if num >= 0 {
            let mut binary_chars = build_binary_string(abs_num);
            
            while binary_chars.len() < w
                invariant
                    binary_chars.len() <= w,
                    is_valid_binary(binary_chars@),
                    binary_chars@ == nat_to_binary_string(abs_num as nat),
            {
                binary_chars.insert(0, '0');
            }
            
            binary_chars
        } else {
            let complement = (modulus as i32 + num) as u32;
            let mut binary_chars = build_binary_string(complement);
            
            while binary_chars.len() < w
                invariant
                    binary_chars.len() <= w,
                    is_valid_binary(binary_chars@),
                    binary_chars@ == nat_to_binary_string(complement as nat),
            {
                binary_chars.insert(0, '0');
            }
            
            binary_chars
        }
    } else {
        if num >= 0 {
            build_binary_string(num as u32)
        } else {
            let mut result = Vec::new();
            result.push('-');
            let abs_digits = build_binary_string((-num) as u32);
            for c in abs_digits {
                result.push(c);
            }
            result
        }
    }
}
// </vc-code>

}
fn main() {}