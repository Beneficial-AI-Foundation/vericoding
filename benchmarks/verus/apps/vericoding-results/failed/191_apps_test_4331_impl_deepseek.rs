// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_mod_7(i: int)
    requires 100 <= i <= 999
decreases i
{
    assert((i / 100) == 7 ==>
        contains_seven(i));
    assert((((i / 10) % 10)) == 7 ==>
        contains_seven(i));
    assert((i % 10) == 7 ==>
        contains_seven(i));
    assert(contains_seven(i) ==>
        ((i / 100) == 7 || ((i / 10) % 10) == 7 || (i % 10) == 7));
}

proof fn lemma_div_mod_bounds(i: int)
    requires 100 <= i <= 999
decreases i
{
    assert(i / 100 >= 1 && i / 100 <= 9);
    assert((i / 10) >= 10 && (i / 10) <= 99);
    assert((i / 10) % 10 >= 0 && (i / 10) % 10 <= 9);
    assert(i % 10 >= 0 && i % 10 <= 9);
}

/* helper modified by LLM (iteration 5): Fixed str_to_vec to properly convert any string to Vec<char> */
fn str_to_vec(s: &str) -> (result: Vec<char>)
    ensures result@ == s@
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == s@.subrange(0, i as int),
        decreases s.len() - i
    {
        v.push(s.as_bytes()[i] as char);
        i += 1;
    }
    v
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ensures clause by returning the result variable */
    proof {
        lemma_div_mod_bounds(n as int);
        lemma_div_mod_7(n as int);
    }
    
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let ones = n % 10;
    
    let result = if hundreds == 7 || tens == 7 || ones == 7 {
        str_to_vec("Yes\n")
    } else {
        str_to_vec("No\n")
    };
    
    result
}
// </vc-code>


}

fn main() {}