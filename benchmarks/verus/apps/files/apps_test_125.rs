// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_newlines(s: Seq<char>, idx: int) -> int
    decreases s.len() - idx
{
    if idx >= s.len() {
        0
    } else if s[idx] == '\n' {
        1 + count_newlines(s, idx + 1)
    } else {
        count_newlines(s, idx + 1)
    }
}

spec fn valid_input_string(s: Seq<char>) -> bool {
    s.len() >= 7 &&
    contains_four_lines(s) &&
    all_lines_have_four_valid_integers(s)
}

spec fn contains_four_lines(s: Seq<char>) -> bool {
    count_newlines(s, 0) >= 3
}

spec fn all_lines_have_four_valid_integers(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

spec fn parse_input(s: Seq<char>, input_lines: Seq<Seq<int>>) -> bool {
    input_lines.len() == 4 &&
    (forall|i: int| 0 <= i < 4 ==> #[trigger] input_lines[i].len() == 4) &&
    (forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
        (#[trigger] input_lines[i][j] >= 0 && #[trigger] input_lines[i][j] <= 1)) &&
    string_contains_four_lines_of_four_integers(s, input_lines)
}

spec fn string_contains_four_lines_of_four_integers(s: Seq<char>, input_lines: Seq<Seq<int>>) -> bool {
    input_lines.len() == 4 &&
    (forall|i: int| 0 <= i < 4 ==> #[trigger] input_lines[i].len() == 4) &&
    valid_input_string(s)
}

spec fn accident_possible(lanes: Seq<Seq<int>>) -> bool
    recommends 
        lanes.len() == 4,
        forall|i: int| 0 <= i < 4 ==> #[trigger] lanes[i].len() == 4,
        forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
            (#[trigger] lanes[i][j] == 0 || #[trigger] lanes[i][j] == 1)
{
    exists|i: int| 0 <= i < 4 && accident_at_lane(i, lanes)
}

spec fn accident_at_lane(i: int, lanes: Seq<Seq<int>>) -> bool
    recommends 
        0 <= i < 4,
        lanes.len() == 4,
        forall|j: int| 0 <= j < 4 ==> #[trigger] lanes[j].len() == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] as int >= 0 && #[trigger] s@[i] as int <= 127),
        valid_input_string(s@)
    ensures 
        result@ == "YES\n"@ || result@ == "NO\n"@,
        exists|input_lines: Seq<Seq<int>>| 
            parse_input(s@, input_lines) && 
            (result@ == "YES\n"@ <==> accident_possible(input_lines)),
        result.len() >= 3
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}