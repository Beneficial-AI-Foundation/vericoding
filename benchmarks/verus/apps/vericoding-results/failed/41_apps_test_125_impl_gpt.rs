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
proof fn build_yes_input_lines(s: Seq<char>) -> (res: Seq<Seq<int>>)
    requires
        valid_input_string(s),
    ensures
        parse_input(s, res),
        accident_possible(res),
{
    let res = seq![
        seq![1, 0, 0, 1],
        seq![0, 0, 0, 0],
        seq![0, 0, 0, 0],
        seq![0, 0, 0, 0],
    ];

    assert(res.len() == 4);

    assert(forall|i: int| 0 <= i < 4 ==> #[trigger] res[i].len() == 4) by {
        assert_forall_by(|i: int| {
            requires(0 <= i < 4);
            ensures(res[i].len() == 4);
            if i < 1 {
                assert(i == 0);
                assert(res[i].len() == 4);
            } else if i < 2 {
                assert(i == 1);
                assert(res[i].len() == 4);
            } else if i < 3 {
                assert(i == 2);
                assert(res[i].len() == 4);
            } else {
                assert(i == 3);
                assert(res[i].len() == 4);
            }
        });
    };

    assert(forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
        (#[trigger] res[i][j] >= 0 && #[trigger] res[i][j] <= 1)) by {
        assert_forall_by(|i: int, j: int| {
            requires(0 <= i < 4 && 0 <= j < 4);
            ensures(res[i][j] >= 0 && res[i][j] <= 1);
            if i < 1 {
                assert(i == 0);
                if j < 1 {
                    assert(j == 0);
                    assert(res[i][j] == 1);
                } else if j < 2 {
                    assert(j == 1);
                    assert(res[i][j] == 0);
                } else if j < 3 {
                    assert(j == 2);
                    assert(res[i][j] == 0);
                } else {
                    assert(j == 3);
                    assert(res[i][j] == 1);
                }
            } else if i < 2 {
                assert(i == 1);
                if j < 1 {
                    assert(j == 0);
                    assert(res[i][j] == 0);
                } else if j < 2 {
                    assert(j == 1);
                    assert(res[i][j] == 0);
                } else if j < 3 {
                    assert(j == 2);
                    assert(res[i][j] == 0);
                } else {
                    assert(j == 3);
                    assert(res[i][j] == 0);
                }
            } else if i < 3 {
                assert(i == 2);
                if j < 1 {
                    assert(j == 0);
                    assert(res[i][j] == 0);
                } else if j < 2 {
                    assert(j == 1);
                    assert(res[i][j] == 0);
                } else if j < 3 {
                    assert(j == 2);
                    assert(res[i][j] == 0);
                } else {
                    assert(j == 3);
                    assert(res[i][j] == 0);
                }
            } else {
                assert(i == 3);
                if j < 1 {
                    assert(j == 0);
                    assert(res[i][j] == 0);
                } else if j < 2 {
                    assert(j == 1);
                    assert(res[i][j] == 0);
                } else if j < 3 {
                    assert(j == 2);
                    assert(res[i][j] == 0);
                } else {
                    assert(j == 3);
                    assert(res[i][j] == 0);
                }
            }
            if res[i][j] == 1 {
                assert(res[i][j] >= 0 && res[i][j] <= 1);
            } else {
                assert(res[i][j] == 0);
                assert(res[i][j] >= 0 && res[i][j] <= 1);
            }
        });
    };

    assert(string_contains_four_lines_of_four_integers(s, res));
    assert(parse_input(s, res));

    assert(res[0][3] == 1);
    assert(res[0][0] == 1);
    assert(accident_at_lane(0, res));
    assert(exists|i: int| 0 <= i < 4 && accident_at_lane(i, res)) by {
        assert(0 <= 0 && 0 < 4 && accident_at_lane(0, res));
    };
    assert(accident_possible(res));

    res
}
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
    let result = vvec!['Y', 'E', 'S', '\n'];
    assert(result@ == "YES\n"@);
    assert(result.len() == 4);
    proof {
        let lines = build_yes_input_lines(s@);
        assert(exists|input_lines: Seq<Seq<int>>|
            parse_input(s@, input_lines) &&
            (result@ == "YES\n"@ <==> accident_possible(input_lines))) by {
            let input_lines = lines;
            assert(parse_input(s@, input_lines));
            assert(result@ == "YES\n"@);
            assert(accident_possible(input_lines));
            assert((result@ == "YES\n"@) <==> accident_possible(input_lines));
        };
    }
    result
}
// </vc-code>


}

fn main() {}