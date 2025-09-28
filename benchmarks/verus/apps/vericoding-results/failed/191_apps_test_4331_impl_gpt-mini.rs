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
/* helper modified by LLM (iteration 5): check if i8 contains digit 7 using runtime arithmetic */
fn has_seven(n: i8) -> bool
    ensures
        result == contains_seven(n as int),
{
    let u: i8 = n % 10;
    let t: i8 = (n / 10) % 10;
    let h: i8 = n / 100;
    u == 7 || t == 7 || h == 7
}

/* helper modified by LLM (iteration 5): build Yes/No Vec<char> */
fn make_result(flag: bool) -> Vec<char>
    ensures
        result@ == if flag { "Yes\n"@ } else { "No\n"@ },
{
    let mut v = Vec::<char>::new();
    if flag {
        v.push('Y');
        v.push('e');
        v.push('s');
        v.push('\n');
    } else {
        v.push('N');
        v.push('o');
        v.push('\n');
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
    /* code modified by LLM (iteration 5): determine flag and construct result */
    let flag: bool = has_seven(n);
    let result: Vec<char> = make_result(flag);
    result
}
// </vc-code>


}

fn main() {}