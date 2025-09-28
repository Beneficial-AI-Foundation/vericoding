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
/* helper modified by LLM (iteration 5): provide base and eve block sequences for reasoning */
spec fn base_string() -> Seq<char> {
    seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's']
}

/* helper modified by LLM (iteration 5): explicit Eve block sequence */
spec fn eve_block() -> Seq<char> {
    seq![' ', 'E', 'v', 'e']
}
// </vc-helpers>

// <vc-spec>
fn solve(d: i8) -> (result: String)
    requires valid_input(d as int)
    ensures result@ == expected_output(d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use standard String::from to build the runtime string */
    let s = if d == 25i8 {
        String::from("Christmas")
    } else if d == 24i8 {
        String::from("Christmas Eve")
    } else if d == 23i8 {
        String::from("Christmas Eve Eve")
    } else {
        String::from("Christmas Eve Eve Eve")
    };

    proof {
        assert(valid_input(d as int));
        if d == 25i8 {
            assert(s@ == seq!['C','h','r','i','s','t','m','a','s']);
            assert(expected_output(d as int) == seq!['C','h','r','i','s','t','m','a','s']);
            assert(s@ == expected_output(d as int));
        } else if d == 24i8 {
            assert(s@ == seq!['C','h','r','i','s','t','m','a','s',' ', 'E','v','e']);
            assert(repeat_eve(1) == seq![' ', 'E','v','e']);
            assert(expected_output(d as int) == seq!['C','h','r','i','s','t','m','a','s'] + repeat_eve(1));
            assert(s@ == expected_output(d as int));
        } else if d == 23i8 {
            assert(s@ == seq!['C','h','r','i','s','t','m','a','s',' ', 'E','v','e',' ', 'E','v','e']);
            assert(repeat_eve(1) == seq![' ', 'E','v','e']);
            assert(repeat_eve(2) == seq![' ', 'E','v','e'] + repeat_eve(1));
            assert(expected_output(d as int) == seq!['C','h','r','i','s','t','m','a','s'] + repeat_eve(2));
            assert(s@ == expected_output(d as int));
        } else {
            assert(d == 22i8);
            assert(s@ == seq!['C','h','r','i','s','t','m','a','s',' ', 'E','v','e',' ', 'E','v','e',' ', 'E','v','e']);
            assert(repeat_eve(1) == seq![' ', 'E','v','e']);
            assert(repeat_eve(2) == seq![' ', 'E','v','e'] + repeat_eve(1));
            assert(repeat_eve(3) == seq![' ', 'E','v','e'] + repeat_eve(2));
            assert(expected_output(d as int) == seq!['C','h','r','i','s','t','m','a','s'] + repeat_eve(3));
            assert(s@ == expected_output(d as int));
        }
    }

    s
}
// </vc-code>


}

fn main() {}