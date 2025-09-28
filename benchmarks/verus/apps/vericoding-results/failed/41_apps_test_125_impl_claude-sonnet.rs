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
spec fn parse_line(line: Seq<char>) -> Seq<int>
    requires line.len() == 7 && line[1] == ' ' && line[3] == ' ' && line[5] == ' ',
             line[0] == '0' || line[0] == '1',
             line[2] == '0' || line[2] == '1',
             line[4] == '0' || line[4] == '1',
             line[6] == '0' || line[6] == '1'
{
    seq![if line[0] == '1' { 1int } else { 0int },
         if line[2] == '1' { 1int } else { 0int },
         if line[4] == '1' { 1int } else { 0int },
         if line[6] == '1' { 1int } else { 0int }]
}

fn check_accident_impl(lanes: Vec<Vec<int>>) -> (result: bool)
    requires lanes.len() == 4,
             forall|i: int| 0 <= i < 4 ==> #[trigger] lanes@[i].len() == 4,
             forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
                 (#[trigger] lanes@[i]@[j] == 0 || #[trigger] lanes@[i]@[j] == 1)
    ensures result == accident_possible(seq![lanes@[0]@, lanes@[1]@, lanes@[2]@, lanes@[3]@])
{
    let mut i = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            forall|k: int| 0 <= k < i ==> !accident_at_lane(k, seq![lanes@[0]@, lanes@[1]@, lanes@[2]@, lanes@[3]@])
    {
        if (lanes[i][3] == 1int && (lanes[i][0] == 1int || lanes[i][1] == 1int || lanes[i][2] == 1int)) ||
           (lanes[i][0] == 1int && lanes[(i + 3) % 4][3] == 1int) ||
           (lanes[i][1] == 1int && lanes[(i + 2) % 4][3] == 1int) ||
           (lanes[i][2] == 1int && lanes[(i + 1) % 4][3] == 1int) {
            return true;
        }
        i += 1;
    }
    false
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
    /* code modified by LLM (iteration 5): fixed integer literal syntax to use explicit int casting */
    let mut lanes: Vec<Vec<int>> = Vec::new();
    let mut line_start = 0;
    let mut line_count = 0;
    
    while line_count < 4
        invariant
            0 <= line_count <= 4,
            lanes.len() == line_count,
            forall|i: int| 0 <= i < line_count ==> #[trigger] lanes@[i].len() == 4,
            line_start <= s.len()
    {
        let mut line_data: Vec<int> = Vec::new();
        let mut pos = 0;
        
        while pos < 4 && line_start + pos * 2 < s.len()
            invariant
                0 <= pos <= 4,
                line_data.len() == pos,
                line_start + pos * 2 <= s.len()
        {
            let char_pos = line_start + pos * 2;
            if char_pos < s.len() {
                if s[char_pos] == '1' {
                    line_data.push(1int);
                } else {
                    line_data.push(0int);
                }
            }
            pos += 1;
        }
        
        lanes.push(line_data);
        
        while line_start < s.len() && s[line_start] != '\n'
            invariant line_start <= s.len()
        {
            line_start += 1;
        }
        line_start += 1;
        line_count += 1;
    }
    
    let has_accident = check_accident_impl(lanes);
    
    if has_accident {
        vec!['Y', 'E', 'S', '\n']
    } else {
        vec!['N', 'O', '\n']
    }
}
// </vc-code>


}

fn main() {}