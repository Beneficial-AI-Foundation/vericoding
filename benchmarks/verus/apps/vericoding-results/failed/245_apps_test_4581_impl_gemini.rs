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
proof fn lemma_count_o_non_negative(s: Seq<char>)
    ensures count_o(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_o_non_negative(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 4): added lemma to prove count_o(s) is bounded by s.len() */
proof fn lemma_count_o_le_len(s: Seq<char>)
    ensures count_o(s) <= s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_o_le_len(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 5): changed signature to use u64 and fixed compilation errors */
fn int_to_string(n: u64) -> (result: Vec<char>)
    ensures
        result@ == int_to_string_spec(n as int),
{
    if n == 0 {
        return vec!['0'];
    }

    let mut num = n;
    let mut res = Vec::new();
    while num > 0
        invariant
            n > 0,
            int_to_string_spec(n as int) == int_to_string_helper_spec(num as int, res@),
        decreases num
    {
        let digit_val = num % 10;
        let digit_char = ((digit_val + 48) as u8) as char;
        res.insert(0, digit_char);
        num = num / 10;
    }
    res
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
/* code modified by LLM (iteration 5): fixed compilation errors by using primitive types */
{
    let mut o_count: u64 = 0;
    let mut i: usize = 0;
    while i < 3
        invariant
            0 <= i <= 3,
            valid_input(s@),
            o_count as int == count_o(s@.subrange(0, i as int)),
        decreases 3 - i
    {
        if s[i] == 'o' {
            o_count = o_count + 1;
        }
        i = i + 1;
    }

    let price = o_count * 100 + 700;

    proof {
        assert(s@.len() == 3);
        assert(s@.subrange(0, 3) == s@);
        assert(o_count as int == count_o(s@));
        assert(price as int == calculate_price(s@));
        lemma_count_o_non_negative(s@);
        assert(calculate_price(s@) >= 700);
    }

    let mut result = int_to_string(price);
    result.push('\n');

    result
}
// </vc-code>


}

fn main() {}