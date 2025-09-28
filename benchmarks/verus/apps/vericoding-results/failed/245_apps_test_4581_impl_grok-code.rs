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
/* helper modified by LLM (iteration 5): added 'int' suffixes to numeric literals for type consistency */
fn count_o_exec(s: Vec<char>) -> (count: int)
    requires
        s.len() == 3,
        forall|i: int| 0 <= i < s.len() ==> (s@[i] == 'o' || s@[i] == 'x')
    ensures
        count == count_o(s@),
        count >= 0,
        count <= 3
{
    let mut i: usize = 0;
    let mut count = 0int;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_o(s@.subrange(0, i as int)),
            count >= 0,
            count <= i as int
        decreases s.len() - i
    {
        if s[i] == 'o' {
            count = count + 1int;
        }
        i = i + 1;
    }
    count
}

/* helper modified by LLM (iteration 5): added 'int' suffixes and fixed char conversion by proper casting */
fn int_to_string_exec(n: int) -> (result: Vec<char>)
    requires
        n >= 0
    ensures
        result@ == int_to_string_spec(n)
{
    if n == 0int {
        let mut v = Vec::new();
        v.push('0');
        v
    } else {
        int_to_string_helper_exec(n, Vec::new())
    }
}

/* helper modified by LLM (iteration 5): added 'int' suffixes and fixed char conversion by proper casting */
fn int_to_string_helper_exec(n: int, acc: Vec<char>) -> (result: Vec<char>)
    requires
        n >= 0
    ensures
        result@ == int_to_string_helper_spec(n, acc@)
    decreases n
{
    if n == 0int {
        acc
    } else {
        let digit_val = n % 10int;
        let digit = (((digit_val as i8) as u8) + 48) as char;
        let mut new_acc = vec![digit];
        new_acc.extend(acc);
        int_to_string_helper_exec(n / 10int, new_acc)
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
/* code modified by LLM (iteration 5): added 'int' suffixes to numeric literals for type consistency */
{
    let count = count_o_exec(s);
    let price = count * 100int + 700int;
    let price_str = int_to_string_exec(price);
    let mut result = price_str;
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}