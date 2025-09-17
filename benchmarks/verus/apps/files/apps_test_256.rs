// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn split_by_char(line: Seq<char>, c: char) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn parse_line(line: Seq<char>) -> Seq<int> {
    Seq::empty()
}

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 4 &&
    (forall|i: int| 0 <= i < 4 ==> valid_player_line(lines[i]))
}

spec fn valid_player_line(line: Seq<char>) -> bool {
    let parts = split_by_char(line, ' ');
    parts.len() == 2 &&
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1])
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9')
}

spec fn compute_result(input: Seq<char>) -> Seq<char> {
    let lines = split_lines(input);
    if lines.len() < 4 {
        Seq::empty()
    } else {
        let player1 = parse_line(lines[0]);
        let player2 = parse_line(lines[1]);
        let player3 = parse_line(lines[2]);
        let player4 = parse_line(lines[3]);

        if player1.len() != 2 || player2.len() != 2 || player3.len() != 2 || player4.len() != 2 {
            Seq::empty()
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
                seq!['T', 'e', 'a', 'm', ' ', '1', '\n']
            } else if team2 {
                seq!['T', 'e', 'a', 'm', ' ', '2', '\n']
            } else {
                seq!['D', 'r', 'a', 'w', '\n']
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
        valid_input(input@)
    ensures
        result@ == compute_result(input@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}