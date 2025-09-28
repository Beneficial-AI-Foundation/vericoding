// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: int, v1: int, v2: int, t1: int, t2: int) -> bool
{
    1 <= s <= 1000 && 1 <= v1 <= 1000 && 1 <= v2 <= 1000 && 1 <= t1 <= 1000 && 1 <= t2 <= 1000
}

spec fn participant_time(s: int, v: int, t: int) -> int
{
    2 * t + s * v
}

spec fn correct_result(s: int, v1: int, v2: int, t1: int, t2: int) -> Seq<char>
{
    let time1 = participant_time(s, v1, t1);
    let time2 = participant_time(s, v2, t2);
    if time1 < time2 { seq!['F','i','r','s','t'] }
    else if time1 > time2 { seq!['S','e','c','o','n','d'] }
    else { seq!['F','r','i','e','n','d','s','h','i','p'] }
}

spec fn valid_result(result: Seq<char>) -> bool
{
    result == seq!['F','i','r','s','t'] || result == seq!['S','e','c','o','n','d'] || result == seq!['F','r','i','e','n','d','s','h','i','p']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Improved type casting and used `spec_index` for sequence access in helper function. */
fn new_vec_from_seq<T>(s: &Seq<T>) -> Vec<T>
    ensures
        new_vec_from_seq(s)@ == s
{
    let mut v = Vec::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant 
            i <= s.len(),
            v@ == s.subsequence(0, i as int),
    {
        v.push(s.spec_index(i));
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(s: i8, v1: i8, v2: i8, t1: i8, t2: i8) -> (result: Vec<char>)
    requires 
        valid_input(s as int, v1 as int, v2 as int, t1 as int, t2 as int)
    ensures 
        valid_result(result@) &&
        result@ == correct_result(s as int, v1 as int, v2 as int, t1 as int, t2 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Modified `time1` and `time2` to be ghost variables to resolve compilation errors. */
{
    let ghost time1: int = (2 * (t1 as int)) + ((s as int) * (v1 as int));
    let ghost time2: int = (2 * (t2 as int)) + ((s as int) * (v2 as int));

    let result_seq: Seq<char>;
    if time1 < time2 {
        result_seq = seq!['F', 'i', 'r', 's', 't'];
    } else if time1 > time2 {
        result_seq = seq!['S', 'e', 'c', 'o', 'n', 'd'];
    } else {
        result_seq = seq!['F', 'r', 'i', 'e', 'n', 'd', 's', 'h', 'i', 'p'];
    }

    new_vec_from_seq(&result_seq)
}
// </vc-code>


}

fn main() {}