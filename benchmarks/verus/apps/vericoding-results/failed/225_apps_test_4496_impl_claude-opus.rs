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
proof fn lemma_repeat_eve_len(count: int)
    requires count >= 0
    ensures repeat_eve(count).len() == 4 * count
    decreases count
{
    if count <= 0 {
        assert(repeat_eve(count) =~= seq![]);
    } else {
        lemma_repeat_eve_len(count - 1);
        assert(repeat_eve(count) =~= seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1));
    }
}

proof fn lemma_repeat_eve_append(count: int)
    requires count > 0
    ensures repeat_eve(count) =~= repeat_eve(count - 1) + seq![' ', 'E', 'v', 'e']
    decreases count
{
    if count == 1 {
        assert(repeat_eve(1) =~= seq![' ', 'E', 'v', 'e'] + repeat_eve(0));
        assert(repeat_eve(0) =~= seq![]);
    } else {
        lemma_repeat_eve_append(count - 1);
        assert(repeat_eve(count) =~= seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1));
        assert(repeat_eve(count - 1) =~= repeat_eve(count - 2) + seq![' ', 'E', 'v', 'e']);
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
    /* code modified by LLM (iteration 5): Using String::from_vec instead of collect() */
    let eve_count: i8 = 25 - d;
    let mut result_vec: Vec<char> = vec!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
    assert(result_vec@ =~= seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's']);
    
    if eve_count == 0 {
        assert(expected_output(d as int) =~= seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's']);
    } else {
        let mut i: i8 = 0;
        while i < eve_count
            invariant
                0 <= i <= eve_count,
                eve_count == 25 - d,
                22 <= d <= 25,
                result_vec@ =~= seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'] + repeat_eve(i as int),
        {
            result_vec.push(' ');
            result_vec.push('E');
            result_vec.push('v');
            result_vec.push('e');
            i = i + 1;
        }
        assert(result_vec@ =~= seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'] + repeat_eve(eve_count as int));
        assert(expected_output(d as int) =~= seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'] + repeat_eve(eve_count as int));
    }
    
    let result: String = String::from_vec(result_vec);
    result
}
// </vc-code>


}

fn main() {}