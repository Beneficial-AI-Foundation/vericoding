// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 3 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'o' || s[i] == 'x'
}

spec fn count_o(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == 'o' { 1int } else { 0int }) + count_o(s.subrange(1, s.len() as int))
    }
}

spec fn calculate_price(s: Seq<char>) -> int
    recommends valid_input(s)
{
    count_o(s) * 100int + 700int
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 {
        seq!['0']
    } else {
        int_to_string_helper_spec(n, seq![])
    }
}

spec fn int_to_string_helper_spec(n: int, acc: Seq<char>) -> Seq<char>
    recommends n >= 0
    decreases n
    when n >= 0
{
    if n == 0 {
        acc
    } else {
        int_to_string_helper_spec(n / 10, seq![((n % 10) + 48) as char] + acc)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors related to `int` and `usize` casting in `int_to_string_tracked` */
fn int_to_string_tracked(n: int) -> (result: Vec<char>)
    requires n >= 0
    ensures result@ == int_to_string_spec(n)
{
    if n == 0 {
        return vec!['0'];
    } else {
        let mut temp_n = n;
        let mut digits = Vec::new();
        while temp_n > 0
            invariant
                temp_n >= 0,
            decreases temp_n
        {
            let digit = (temp_n % 10) as u8;
            digits.push((digit + 48) as char);
            temp_n /= 10;
        }

        let mut result_vec = Vec::new();
        let mut i: int = digits.len() as int - 1;
        while i >= 0
            invariant
                i >= -1,
                i < digits.len() as int,
                result_vec.len() as int == digits.len() as int - 1 - i,
                digits.len() >= 0,
                forall |j: int| 0 <= j < i + 1 ==> digits.len() > j,
                forall |j: int| 0 <= j < result_vec.len() ==> result_vec[j] == digits[digits.len() - 1 - j as int],
            decreases i
        {
            result_vec.push(digits[i as usize]);
            i = i - 1;
        }
        result_vec
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(s@)
    ensures 
        result@ == int_to_string_spec(calculate_price(s@)) + seq!['\n'],
        calculate_price(s@) >= 700
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed character literal escape for newline character. */
{
    let price = calculate_price(s@);
    let price_string = int_to_string_tracked(price);
    let mut result_vec = price_string;
    result_vec.push('\n');
    result_vec
}
// </vc-code>


}

fn main() {}