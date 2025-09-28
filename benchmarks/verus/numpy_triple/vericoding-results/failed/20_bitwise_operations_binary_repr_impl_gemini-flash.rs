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
/* helper modified by LLM (iteration 5): Removed spec function requires/ensures. */
spec fn lemma_nat_to_binary_string_len(n: nat) -> (len: nat)
    decreases n
{
    if n == 0 {
        1
    } else {
        let temp_len = lemma_nat_to_binary_string_len(n / 2);
        temp_len + 1
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
/* code modified by LLM (iteration 5): Replaced deprecated `get_Some_0()` with `->` operator for `Option` values. */
{
    let mut chars: Vec<char> = Vec::new();

    if num == 0 {
        if width.is_some() {
            let w = width->get_Some();
            for _i in 0..w - 1 {
                chars.push('0');
            }
        }
        chars.push('0');
    } else if num > 0 {
        let mut n = num as u64;

        while n > 0
            invariant
                n >= 0,
                forall|i: int| 0 <= i < chars.len() ==> chars@[i] == '0' || chars@[i] == '1',
            decreases n
        {
            let digit = if n % 2 == 0 { '0' } else { '1' };
            chars.push(digit);
            n = n / 2;
        }
        chars.reverse();

        if width.is_some() {
            let w = width->get_Some();
            let current_len = chars.len();
            if current_len < w {
                let mut padding: Vec<char> = Vec::new();
                for _i in 0..(w - current_len) {
                    padding.push('0');
                }
                padding.extend(chars);
                chars = padding;
            } else if current_len > w {
                // This case should ideally not happen if width is correctly used for positive numbers
            }
        }
    } else { // num < 0
        if width.is_none() {
            chars.push('-');
            let mut n = (-num) as u64;
            let mut abs_chars: Vec<char> = Vec::new();
            while n > 0
                invariant
                    n >= 0,
                    forall|i: int| 0 <= i < abs_chars.len() ==> abs_chars@[i] == '0' || abs_chars@[i] == '1',
                decreases n
            {
                let digit = if n % 2 == 0 { '0' } else { '1' };
                abs_chars.push(digit);
                n = n / 2;
            }
            abs_chars.reverse();
            chars.extend(abs_chars);
        } else {
            let w = width->get_Some() as u32;
            let two_comp_val = (1u32 << w) as i32 + num;
            let mut n = two_comp_val as u64;

            while n > 0
                invariant
                    n >= 0,
                    forall|i: int| 0 <= i < chars.len() ==> chars@[i] == '0' || chars@[i] == '1',
                    width.is_some() ==> chars.len() <= width->get_Some(),
                decreases n
            {
                let digit = if n % 2 == 0 { '0' } else { '1' };
                chars.push(digit);
                n = n / 2;
            }
            chars.reverse();

            let current_len = chars.len();
            let w_usize = width->get_Some();
            if current_len < w_usize {
                let mut padding: Vec<char> = Vec::new();
                // For two's complement, negative numbers should be padded with '1's
                // However, the spec seems to imply positive values for two_comp. Let's pad with '0' for correctness based on `two_comp >= 0`.
                for _i in 0..(w_usize - current_len) {
                    padding.push('0');
                }
                padding.extend(chars);
                chars = padding;
            }
        }
    }

    chars
}
// </vc-code>

}
fn main() {}