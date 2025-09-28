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
/* helper modified by LLM (iteration 5): count_o_vec returns usize matching count_o spec */
fn count_o_vec(s: &Vec<char>) -> (r: usize)
    requires
        valid_input(s@),
    ensures
        (r as int) == count_o(s@),
    decreases
        s.len() as int
{
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            (cnt as int) == count_o(s@.subrange(0, i as int)),
        decreases (s.len() as int - i as int)
    {
        if s[i] == 'o' {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}

/* helper modified by LLM (iteration 5): int_to_vec converts usize to Vec<char> matching int_to_string_spec */
fn int_to_vec(n: usize) -> (result: Vec<char>)
    ensures
        result@ == int_to_string_spec(n as int),
    decreases
        n
{
    if n == 0 {
        let res = vec!['0'];
        res
    } else {
        let res = int_to_vec_rec(n);
        res
    }
}

/* helper modified by LLM (iteration 5): int_to_vec_rec recursive conversion for usize > 0 */
fn int_to_vec_rec(n: usize) -> (result: Vec<char>)
    requires
        n > 0,
    ensures
        result@ == int_to_string_helper_spec(n as int, seq![]),
    decreases
        n
{
    if n / 10 == 0 {
        let d = ((n % 10) + 48) as char;
        let res = vec![d];
        res
    } else {
        let mut v = int_to_vec_rec(n / 10);
        v.push(((n % 10) + 48) as char);
        v
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
    /* code modified by LLM (iteration 5): compute price using usize helpers and append newline */
    let cnt = count_o_vec(&s);
    let price: usize = cnt * 100usize + 700usize;
    let mut v = int_to_vec(price);
    v.push('\n');
    let result = v;
    result
}

// </vc-code>


}

fn main() {}