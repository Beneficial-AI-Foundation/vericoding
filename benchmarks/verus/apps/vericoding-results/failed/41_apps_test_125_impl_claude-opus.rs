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
/* helper modified by LLM (iteration 4): Added decreases clause to while loop in parse_line */
spec fn vec_to_seq_lanes(lanes: Seq<Vec<i32>>) -> Seq<Seq<int>>
    recommends
        lanes.len() == 4,
        forall|i: int| 0 <= i < 4 ==> #[trigger] lanes[i].len() == 4
{
    seq![
        seq![lanes[0]@[0] as int, lanes[0]@[1] as int, lanes[0]@[2] as int, lanes[0]@[3] as int],
        seq![lanes[1]@[0] as int, lanes[1]@[1] as int, lanes[1]@[2] as int, lanes[1]@[3] as int],
        seq![lanes[2]@[0] as int, lanes[2]@[1] as int, lanes[2]@[2] as int, lanes[2]@[3] as int],
        seq![lanes[3]@[0] as int, lanes[3]@[1] as int, lanes[3]@[2] as int, lanes[3]@[3] as int]
    ]
}

spec fn char_to_int(c: char) -> int {
    if c == '0' { 0 } else { 1 }
}

fn parse_line(s: &Vec<char>, start: usize, end: usize) -> (result: Vec<i32>)
    requires
        start < end,
        end <= s.len(),
        end - start >= 7,
        forall|i: int| start <= i < end ==> (#[trigger] s@[i] == '0' || #[trigger] s@[i] == '1' || #[trigger] s@[i] == ' ' || #[trigger] s@[i] == '\n')
    ensures
        result.len() == 4,
        forall|i: int| 0 <= i < 4 ==> (#[trigger] result@[i] >= 0 && #[trigger] result@[i] <= 1)
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = start;
    
    while i < end && nums.len() < 4
        invariant
            start <= i <= end,
            nums.len() <= 4,
            forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums@[j] >= 0 && #[trigger] nums@[j] <= 1)
        decreases end - i
    {
        if s[i] == '0' {
            nums.push(0);
        } else if s[i] == '1' {
            nums.push(1);
        }
        i = i + 1;
    }
    
    while nums.len() < 4
        invariant
            nums.len() <= 4,
            forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums@[j] >= 0 && #[trigger] nums@[j] <= 1)
        decreases 4 - nums.len()
    {
        nums.push(0);
    }
    
    nums
}

fn parse_all_lines(s: &Vec<char>) -> (result: Vec<Vec<i32>>)
    requires
        s.len() >= 7,
        valid_input_string(s@)
    ensures
        result.len() == 4,
        forall|i: int| 0 <= i < 4 ==> #[trigger] result@[i].len() == 4,
        forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
            (#[trigger] result@[i]@[j] >= 0 && #[trigger] result@[i]@[j] <= 1)
{
    let mut lines: Vec<Vec<i32>> = Vec::new();
    let mut start: usize = 0;
    let mut line_count: usize = 0;
    
    let mut i: usize = 0;
    while i < s.len() && line_count < 4
        invariant
            0 <= i <= s.len(),
            0 <= start <= i,
            line_count <= 4,
            lines.len() == line_count,
            forall|j: int| 0 <= j < lines.len() ==> #[trigger] lines@[j].len() == 4,
            forall|j: int, k: int| 0 <= j < lines.len() && 0 <= k < 4 ==> 
                (#[trigger] lines@[j]@[k] >= 0 && #[trigger] lines@[j]@[k] <= 1)
        decreases s.len() - i
    {
        if s[i] == '\n' || i == s.len() - 1 {
            let end = if s[i] == '\n' { i } else { i + 1 };
            if end > start {
                let line = parse_line(s, start, end);
                lines.push(line);
                line_count = line_count + 1;
                start = i + 1;
            }
        }
        i = i + 1;
    }
    
    while lines.len() < 4
        invariant
            lines.len() <= 4,
            forall|j: int| 0 <= j < lines.len() ==> #[trigger] lines@[j].len() == 4,
            forall|j: int, k: int| 0 <= j < lines.len() && 0 <= k < 4 ==> 
                (#[trigger] lines@[j]@[k] >= 0 && #[trigger] lines@[j]@[k] <= 1)
        decreases 4 - lines.len()
    {
        let mut empty_line: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < 4
            invariant
                j <= 4,
                empty_line.len() == j,
                forall|k: int| 0 <= k < empty_line.len() ==> #[trigger] empty_line@[k] == 0
            decreases 4 - j
        {
            empty_line.push(0);
            j = j + 1;
        }
        lines.push(empty_line);
    }
    
    lines
}

fn check_accident(lanes: &Vec<Vec<i32>>) -> (result: bool)
    requires
        lanes.len() == 4,
        forall|i: int| 0 <= i < 4 ==> #[trigger] lanes@[i].len() == 4,
        forall|i: int, j: int| 0 <= i < 4 && 0 <= j < 4 ==> 
            (#[trigger] lanes@[i]@[j] >= 0 && #[trigger] lanes@[i]@[j] <= 1)
    ensures
        result <==> accident_possible(vec_to_seq_lanes(lanes@))
{
    let mut i: usize = 0;
    let mut found: bool = false;
    
    while i < 4
        invariant
            i <= 4,
            found <==> exists|j: int| 0 <= j < i && accident_at_lane(j, vec_to_seq_lanes(lanes@))
        decreases 4 - i
    {
        if lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1) {
            found = true;
        } else if lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1 {
            found = true;
        } else if lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1 {
            found = true;
        } else if lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1 {
            found = true;
        }
        i = i + 1;
    }
    
    found
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
    /* code modified by LLM (iteration 4): No changes to main code body */
    let lanes = parse_all_lines(&s);
    let accident = check_accident(&lanes);
    
    if accident {
        let mut result = Vec::new();
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
        assert(result@ == "YES\n"@);
        result
    } else {
        let mut result = Vec::new();
        result.push('N');
        result.push('O');
        result.push('\n');
        assert(result@ == "NO\n"@);
        result
    }
}
// </vc-code>


}

fn main() {}