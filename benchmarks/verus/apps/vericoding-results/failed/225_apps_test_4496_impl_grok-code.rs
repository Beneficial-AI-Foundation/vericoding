// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(d: int) -> bool {
    22 <= d <= 25
}

spec fn expected_output(d: int) -> Seq<char> {
    if valid_input(d) {
        let eve_count = 25 - d;
        let base_string = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
        if eve_count == 0 {
            base_string
        } else {
            base_string + repeat_eve(eve_count)
        }
    } else {
        seq![]
    }
}

spec fn repeat_eve(count: int) -> Seq<char>
    decreases count
{
    if count <= 0 {
        seq![]
    } else {
        seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable version of repeat_eve spec */
fn build_eve(count: int) -> (result: Seq<char>)
    decreases count
    requires
        count >= 0
    ensures
        result == repeat_eve(count),
{
    if count <= 0 {
        seq![]
    } else {
        seq![' ', 'E', 'v', 'e'] + build_eve(count - 1)
    }
}

/* helper modified by LLM (iteration 5): executable version of seq to string spec */
fn seq_to_string(s: Seq<char>) -> (result: String)
    ensures
        result@.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> result@[i] == s[i],
{
    let mut result = String::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == s[j],
        decreases s.len() - i
    {
        let c = s[i];
        result.push(c);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(d: i8) -> (result: String)
    requires valid_input(d as int)
    ensures result@ == expected_output(d as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implemented christmas eve string construction */
    let eve_count = 25 - (d as int);
    let base = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
    let eves = if eve_count <= 0 {
        seq![]
    } else {
        build_eve(eve_count)
    };
    let sequence = base + eves;
    let result = seq_to_string(sequence);
    result
}
// </vc-code>


}

fn main() {}