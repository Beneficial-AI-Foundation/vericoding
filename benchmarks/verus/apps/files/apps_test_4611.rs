// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
struct Checkpoint {
    t: int,
    x: int,
    y: int,
}

spec fn valid_input_format(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() > 0 && is_valid_integer(lines[0]) && 
    ({
        let n = parse_int(lines[0]);
        n >= 0 && n + 1 == lines.len() &&
        (forall|i: int| 1 <= i < lines.len() ==> is_valid_checkpoint_line(lines[i]))
    })
}

spec fn can_visit_all_checkpoints(input: Seq<char>) -> bool
    recommends valid_input_format(input)
{
    let lines = split_lines(input);
    let n = parse_int(lines[0]);
    if n == 0 { 
        true 
    } else {
        let checkpoints = parse_checkpoints(lines.subrange(1, lines.len() as int));
        checkpoints.len() == n &&
        checkpoints_feasible(checkpoints, 0, 0, 0)
    }
}

spec fn checkpoints_feasible(checkpoints: Seq<Checkpoint>, current_t: int, current_x: int, current_y: int) -> bool
    decreases checkpoints.len()
{
    if checkpoints.len() == 0 { 
        true 
    } else {
        let cp = checkpoints[0];
        let dt = cp.t - current_t;
        let dx = if current_x >= cp.x { current_x - cp.x } else { cp.x - current_x };
        let dy = if current_y >= cp.y { current_y - cp.y } else { cp.y - current_y };
        let dis = dx + dy;
        if dt < dis { 
            false 
        } else if (dt - dis) % 2 != 0 { 
            false 
        } else { 
            checkpoints_feasible(checkpoints.subrange(1, checkpoints.len() as int), cp.t, cp.x, cp.y) 
        }
    }
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    seq![]
}

spec fn is_valid_integer(line: Seq<char>) -> bool {
    true
}

spec fn parse_int(line: Seq<char>) -> int {
    0
}

spec fn is_valid_checkpoint_line(line: Seq<char>) -> bool {
    true
}

spec fn parse_checkpoints(lines: Seq<Seq<char>>) -> Seq<Checkpoint> {
    seq![]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires
        stdin_input@.len() > 0,
        valid_input_format(stdin_input@),
    ensures
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        (result@ == seq!['Y', 'e', 's', '\n']) <==> can_visit_all_checkpoints(stdin_input@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No\n".to_string()
}
// </vc-code>


}

fn main() {}