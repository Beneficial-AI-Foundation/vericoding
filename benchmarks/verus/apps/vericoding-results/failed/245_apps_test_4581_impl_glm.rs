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
/* helper modified by LLM (iteration 4): fixed integer type conversion in int_to_string_exec */
fn count_o_vec(v: &Vec<char>) -> (count: int)
    ensures count == count_o(v@)
{
    let mut count: int = 0int;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            count == count_o(v@.subrange(0, i as int)),
        decreases v.len() - i
    {
        if v[i] == 'o' {
            count += 1int;
        }
        i += 1;
    }
    count
}

fn calculate_price_vec(v: &Vec<char>) -> (price: int)
    ensures price == calculate_price(v@)
{
    let count = count_o_vec(v);
    count * 100int + 700int
}

fn int_to_string_exec(n: int) -> (s: Vec<char>)
    requires n >= 0
    ensures s@ == int_to_string_spec(n)
    decreases n
{
    if n == 0int {
        vec!['0']
    } else if n < 10int {
        let n_rust = n as u8;
        vec![(n_rust + 48u8) as char]
    } else {
        let n_rust = n as u64;
        let rest = int_to_string_exec((n_rust / 10) as int);
        let last_digit = (n_rust % 10) as u8;
        let mut result = rest;
        result.push((last_digit + 48u8) as char);
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
/* code modified by LLM (iteration 4): no changes needed - helper fixed */
{
    let price = calculate_price_vec(&s);
    let mut str_vec = int_to_string_exec(price);
    str_vec.push('\n');
    str_vec
}
// </vc-code>


}

fn main() {}