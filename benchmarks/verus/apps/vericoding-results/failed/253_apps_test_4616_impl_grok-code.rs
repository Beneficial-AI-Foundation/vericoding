// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_abbreviation(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() >= 3 &&
    s.len() >= 3 &&
    result[0] == s[0] &&
    result[result.len() - 1] == s[s.len() - 1] &&
    result == seq![s[0]].add(int_to_string(s.len() - 2)).add(seq![s[s.len() - 1]])
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        Seq::new(0 as nat, |_i: int| ' ')
    } else {
        int_to_string_helper(n / 10).add(seq![(('0' as int) + (n % 10)) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by manually reversing the digits vector */
fn usize_to_string(n: usize) -> Vec<char>
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0 {
            let digit = char::from_u32(('0' as u32) + ((num % 10) as u32)).unwrap();
            digits.push(digit);
            num /= 10;
        }
        let len = digits.len();
        let mut result = Vec::with_capacity(len);
        let mut i = (len as int) - 1;
        while i >= 0 {
            result.push(digits[i as int]);
            i = i - 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed */
{
    let first = s[0];
    let last = s[s.len() - 1];
    let mid_len = s.len() - 2;
    let mid_str = usize_to_string(mid_len);
    let mut result = Vec::new();
    result.push(first);
    let mut temp = mid_str.clone();
    result.append(&mut temp);
    result.push(last);
    result
}
// </vc-code>


}

fn main() {}