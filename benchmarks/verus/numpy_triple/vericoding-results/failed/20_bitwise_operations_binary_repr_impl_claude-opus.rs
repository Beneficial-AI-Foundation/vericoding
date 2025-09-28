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
    /* code modified by LLM (iteration 4): Fixed overflow issue and postcondition verification */
    if width.is_none() {
        if num >= 0 {
            let mut n = num as u32;
            let mut result = Vec::new();
            if n == 0 {
                result.push('0');
            } else {
                let mut chars = Vec::new();
                while n > 0
                    invariant
                        n >= 0,
                        forall|j: int| 0 <= j < chars.len() ==> (chars[j] == '0' || chars[j] == '1')
                    decreases n
                {
                    if n % 2 == 0 {
                        chars.push('0');
                    } else {
                        chars.push('1');
                    }
                    n = n / 2;
                }
                let mut i = chars.len();
                while i > 0
                    invariant
                        i <= chars.len(),
                        result.len() == chars.len() - i,
                        forall|j: int| 0 <= j < result.len() ==> (result[j] == '0' || result[j] == '1')
                    decreases i
                {
                    i = i - 1;
                    result.push(chars[i]);
                }
            }
            assert(is_valid_binary(result@));
            assert(is_valid_signed_binary(result@));
            result
        } else {
            // Handle overflow case for i32::MIN
            let mut n = if num == i32::MIN {
                (i32::MAX as u32) + 1
            } else {
                (-(num as i64)) as u32
            };
            let mut result = Vec::new();
            result.push('-');
            if n == 0 {
                result.push('0');
            } else {
                let mut chars = Vec::new();
                while n > 0
                    invariant
                        n >= 0,
                        forall|j: int| 0 <= j < chars.len() ==> (chars[j] == '0' || chars[j] == '1')
                    decreases n
                {
                    if n % 2 == 0 {
                        chars.push('0');
                    } else {
                        chars.push('1');
                    }
                    n = n / 2;
                }
                let mut i = chars.len();
                while i > 0
                    invariant
                        i <= chars.len(),
                        result.len() == chars.len() - i + 1,
                        result[0] == '-',
                        forall|j: int| 1 <= j < result.len() ==> (result[j] == '0' || result[j] == '1')
                    decreases i
                {
                    i = i - 1;
                    result.push(chars[i]);
                }
            }
            assert(result@[0] == '-');
            assert(is_valid_binary(result@.skip(1)));
            assert(is_valid_signed_binary(result@));
            result
        }
    } else {
        match width {
            Some(w) => {
                let mut val = if num >= 0 {
                    num as u32
                } else {
                    #[verifier::truncate]
                    ((#[verifier::truncate] (1u32 << w) as i32) + num) as u32
                };
                let mut result = Vec::new();
                let mut i: usize = 0;
                while i < w
                    invariant
                        i <= w,
                        result.len() == i,
                        forall|j: int| 0 <= j < i ==> result[j] == '0'
                    decreases w - i
                {
                    result.push('0');
                    i = i + 1;
                }
                let mut pos = w;
                while pos > 0
                    invariant
                        pos <= w,
                        result.len() == w,
                        forall|j: int| 0 <= j < result.len() ==> (result[j] == '0' || result[j] == '1')
                    decreases pos
                {
                    pos = pos - 1;
                    if val % 2 == 0 {
                        result.set(pos, '0');
                    } else {
                        result.set(pos, '1');
                    }
                    val = val / 2;
                }
                assert(is_valid_binary(result@));
                result
            },
            None => unreached()
        }
    }
}
// </vc-code>

}
fn main() {}