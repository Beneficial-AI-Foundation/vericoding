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
/* helper modified by LLM (iteration 5): fixed valid_input preservation for subrange and invariant maintenance */
proof fn lemma_count_o_bounds(s: Seq<char>)
    requires valid_input(s)
    ensures 0 <= count_o(s) <= 3
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        // For the recursive call to be valid, we need the subrange to have valid structure
        // but it won't satisfy the full valid_input predicate (wrong length)
        // Instead, we reason about the recursive structure directly
        lemma_count_o_bounds_helper(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_count_o_bounds_helper(s: Seq<char>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == 'o' || s[i] == 'x'
    ensures 0 <= count_o(s) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_o_bounds_helper(s.subrange(1, s.len() as int));
    }
}

fn count_o_impl(s: &Vec<char>) -> (result: usize)
    requires valid_input(s@)
    ensures result as int == count_o(s@)
{
    let mut count: usize = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_o(s@.subrange(0, i as int)),
            count <= i
        decreases s.len() - i
    {
        if s[i] == 'o' {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn int_to_string_impl(n: usize) -> (result: Vec<char>)
    requires n >= 700
    ensures result@ == int_to_string_spec(n as int)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        let original_n = n;
        while num > 0
            invariant
                result@.len() <= 10,
                int_to_string_helper_spec(num as int, result@) == int_to_string_spec(original_n as int),
                num <= original_n,
                original_n == n
            decreases num
        {
            let digit = (num % 10) as u8 + 48;
            result.insert(0, digit as char);
            num = num / 10;
        }
        result
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
{
    /* code modified by LLM (iteration 5): fixed recursive lemma call and added bound check for count */
    proof {
        lemma_count_o_bounds(s@);
    }
    let count = count_o_impl(&s);
    let price = count * 100 + 700;
    let mut result = int_to_string_impl(price);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}