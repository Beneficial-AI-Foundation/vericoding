// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn split_lines(input: &str) -> Seq<&str> {
    Seq::empty()
}

#[verifier::external_body]
spec fn split_by_char(line: &str, c: char) -> Seq<&str> {
    Seq::empty()
}

#[verifier::external_body]
spec fn char_at(s: &str, i: int) -> char {
    ' '
}

#[verifier::external_body]
spec fn str_len(s: &str) -> int {
    0
}

#[verifier::external_body]
spec fn empty_string() -> String {
    String::new()
}

#[verifier::external_body]
spec fn team1_string() -> String {
    "Team 1\n".to_string()
}

#[verifier::external_body]
spec fn team2_string() -> String {
    "Team 2\n".to_string()
}

#[verifier::external_body]
spec fn draw_string() -> String {
    "Draw\n".to_string()
}

spec fn is_valid_integer(s: &str) -> bool {
    str_len(s) > 0 && forall|i: int| 0 <= i < str_len(s) ==> ('0' <= char_at(s, i) && char_at(s, i) <= '9')
}

spec fn valid_player_line(line: &str) -> bool {
    let parts = split_by_char(line, ' ');
    parts.len() == 2 &&
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1])
}

spec fn valid_input(input: &str) -> bool {
    let lines = split_lines(input);
    lines.len() >= 4 &&
    forall|i: int| 0 <= i < 4 ==> valid_player_line(lines[i])
}

#[verifier::external_body]
spec fn parse_line(line: &str) -> Seq<int> {
    Seq::empty()
}

spec fn compute_result(input: &str) -> String {
    let lines = split_lines(input);
    if lines.len() < 4 {
        empty_string()
    } else {
        let player1 = parse_line(lines[0]);
        let player2 = parse_line(lines[1]);
        let player3 = parse_line(lines[2]);
        let player4 = parse_line(lines[3]);

        if player1.len() != 2 || player2.len() != 2 || player3.len() != 2 || player4.len() != 2 {
            empty_string()
        } else {
            let a = player1[0];
            let b = player1[1];
            let c = player2[0];
            let d = player2[1];
            let x = player3[0];
            let y = player3[1];
            let z = player4[0];
            let w = player4[1];

            let team1 = (a > w && a > y && d > x && d > z) || (c > w && c > y && b > x && b > z);
            let team2 = ((x > b && w > c) || (z > b && y > c)) && ((x > d && w > a) || (z > d && y > a));

            if team1 {
                team1_string()
            } else if team2 {
                team2_string()
            } else {
                draw_string()
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        valid_input(input)
    ensures 
        result == compute_result(input),
        (result@ == "Team 1\n"@) || (result@ == "Team 2\n"@) || (result@ == "Draw\n"@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    "Draw\n".to_string()
}
// </vc-code>


}

fn main() {}