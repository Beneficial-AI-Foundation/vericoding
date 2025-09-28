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
proof fn lemma_repeat_eve_len(count: nat)
    ensures repeat_eve(count)@.len() == 4 * count as int,
    decreases count
{
    if count > 0 {
        lemma_repeat_eve_len((count - 1) as nat);
    }
}

proof fn lemma_repeat_eve_content(count: nat, i: int)
    requires 0 <= i < 4 * count as int,
    ensures repeat_eve(count)@[i] == match i % 4 {
        0 => ' ',
        1 => 'E',
        2 => 'v',
        _ => 'e'
    },
    decreases count
{
    if count > 0 {
        if i < 4 {
            // Base case
        } else {
            lemma_repeat_eve_content((count - 1) as nat, i - 4);
        }
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
    /* code modified by LLM (iteration 5): fix compilation error by removing ghost function */
    let ghost d_val = d as int;
    let mut result = String::from("Christmas");
    
    let mut count: u8 = 0;
    while count < (25 - d) as u8
        invariant
            count <= (25 - d) as u8,
            result@ == seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'] + repeat_eve(count as int)
    {
        result.push_str(" Eve");
        count += 1;
    }
    
    proof {
        lemma_repeat_eve_len((25 - d_val) as nat);
        assert(result@ == expected_output(d_val));
    }
    
    result
}
// </vc-code>


}

fn main() {}