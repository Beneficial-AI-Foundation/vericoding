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
/* helper modified by LLM (iteration 5): lemma about repeat_eve recursion */
proof fn repeat_eve_def(count: int)
    requires
        count >= 0,
    ensures
        repeat_eve(count) == if count == 0 { seq![] } else { seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1) },
    decreases
        count
{
    if count == 0 {
    } else {
        repeat_eve_def(count - 1);
    }
}

/* helper modified by LLM (iteration 5): lemma relating expected_output to base and repeats for valid d */
proof fn expected_output_decomp(d: int)
    requires
        valid_input(d),
    ensures
        expected_output(d) == {
            let eve_count = 25 - d;
            let base_string = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
            if eve_count == 0 { base_string } else { base_string + repeat_eve(eve_count) }
        },
    decreases
        25 - d
{
    let eve_count = 25 - d;
    if eve_count <= 0 {
    } else {
        repeat_eve_def(eve_count);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(d: i8) -> (result: String)
    requires valid_input(d as int)
    ensures result@ == expected_output(d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build String by pushing characters from expected_output */
    let seq_chars = expected_output(d as int);
    let mut result = String::new();
    let mut i: nat = 0;
    let n: nat = seq_chars.len();
    while i < n
        invariant
            i <= n,
            result@ == seq_chars[..i],
        decreases
            n - i
    {
        result.push_char(seq_chars@[i]);
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}