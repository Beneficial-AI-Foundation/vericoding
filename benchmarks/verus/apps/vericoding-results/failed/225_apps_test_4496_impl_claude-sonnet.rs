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
/* helper modified by LLM (iteration 5): fixed lemma declaration syntax with exclamation mark */
lemma lemma_repeat_eve_length!(count: int)
    requires count >= 0
    ensures repeat_eve(count).len() == 4 * count
    decreases count
{
    if count > 0 {
        lemma_repeat_eve_length!(count - 1);
    }
}

lemma lemma_repeat_eve_concat_property!(count: int)
    requires count > 0
    ensures repeat_eve(count) == seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1)
    decreases count
{
}

fn build_eve_string(eve_count: usize) -> (result: String)
    requires eve_count <= 3
    ensures result@.len() == 4 * eve_count
    ensures result@ == repeat_eve(eve_count as int)
{
    if eve_count == 0 {
        String::new()
    } else {
        let mut s = String::new();
        let mut i = 0;
        while i < eve_count
            invariant
                i <= eve_count,
                s@.len() == 4 * i,
                s@ == repeat_eve(i as int)
        {
            s.push(' ');
            s.push('E');
            s.push('v');
            s.push('e');
            i += 1;
        }
        s
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
    /* code modified by LLM (iteration 5): fixed implementation */
    let base = "Christmas";
    let eve_count = (25 - d) as usize;
    
    if eve_count == 0 {
        base.to_string()
    } else {
        let eve_part = build_eve_string(eve_count);
        let mut result = base.to_string();
        result.push_str(&eve_part);
        result
    }
}
// </vc-code>


}

fn main() {}