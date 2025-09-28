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
/* helper modified by LLM (iteration 5): fixed integer type handling in while loop */
fn int_to_string(n: int) -> (result: Vec<char>)
    requires
        n >= 0,
    ensures
        result@ == int_to_string_spec(n),
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut temp = n;
        let mut acc: Vec<char> = Vec::new();
        
        while temp > 0
            invariant
                temp >= 0,
                temp <= n,
                acc@ == int_to_string_helper_spec(temp, seq![]),
            decreases temp
        {
            let digit_int = temp % 10;
            let digit_char = ((digit_int + 48) as u8) as char;
            let mut new_acc = Vec::new();
            new_acc.push(digit_char);
            for i in 0..acc.len() {
                new_acc.push(acc[i]);
            }
            acc = new_acc;
            temp = temp / 10;
        }
        acc
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
/* code modified by LLM (iteration 5): fixed type cast and loop index handling */
{
    let mut count: int = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            count == count_o(s@.subrange(0, i as int)),
    {
        if s[i] == 'o' {
            count = count + 1;
        }
        i = i + 1;
    }
    let total_price = count * 100 + 700;
    let result_string = int_to_string(total_price);
    let mut final_result = Vec::new();
    for j in 0..result_string.len() {
        final_result.push(result_string[j]);
    }
    final_result.push('\n');
    final_result
}
// </vc-code>


}

fn main() {}