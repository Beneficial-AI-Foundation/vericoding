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
/* helper modified by LLM (iteration 5): Fixed type mismatches, usize conversions, and indexing syntax */
fn parse_four_integers(s: &Vec<char>, start_idx: &mut usize) -> (result: Vec<int>)
    ensures
        result@.len() == 4,
        forall|j: int| 0 <= j < 4 ==> #[trigger] result@[j] == 0 || #[trigger] result@[j] == 1
{
    let mut result: Vec<int> = Vec::new();
    let mut idx = *start_idx;
    let mut count = 0;
    
    while count < 4 && idx < s.len()
        invariant
            idx <= s.len(),
            count <= 4,
            result@.len() == count,
            forall|j: int| 0 <= j < count ==> #[trigger] result@[j] == 0 || #[trigger] result@[j] == 1
        decreases s.len() - idx
    {
        if s[idx] == '0' {
            result.push(0 as int);
            count += 1;
        } else if s[idx] == '1' {
            result.push(1 as int);
            count += 1;
        }
        idx = idx + 1;
    }
    
    *start_idx = idx;
    result
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
/* code modified by LLM (iteration 5): Fixed type mismatches, usize conversions, indexing syntax, and std::ops imports */
{
    use std::ops::Index;
    use std::ops::IndexMut;
    
    let mut lanes = Vec::new();
    lanes.push(Vec::new());
    lanes.push(Vec::new());
    lanes.push(Vec::new());
    lanes.push(Vec::new());
    
    let mut idx: usize = 0;
    let mut row = 0;
    
    while idx < s.len() && row < 4
        invariant
            idx <= s.len(),
            0 <= row <= 4,
            lanes@.len() == 4,
            forall|i: int| 0 <= i < 4 ==> lanes@[i].len() == if i < row { 4 } else { 0 }
        decreases s.len() - idx
    {
        let mut start_idx = idx;
        let line = parse_four_integers(&s, &mut start_idx);
        idx = start_idx;
        
        if row < 4 && line.len() == 4 {
            lanes.index_mut(row).extend(line);
            row += 1;
        }
        
        while idx < s.len() && s.index(idx) != '\n' {
            idx = idx + 1;
        }
        if idx < s.len() && s.index(idx) == '\n' {
            idx = idx + 1;
        }
    }
    
    let mut accident = false;
    
    for i in 0..4 {
        accident = accident || (
            (lanes.index(i).index(3) == 1 && (lanes.index(i).index(0) == 1 || lanes.index(i).index(1) == 1 || lanes.index(i).index(2) == 1)) ||
            (lanes.index(i).index(0) == 1 && lanes.index((i + 3) % 4).index(3) == 1) ||
            (lanes.index(i).index(1) == 1 && lanes.index((i + 2) % 4).index(3) == 1) ||
            (lanes.index(i).index(2) == 1 && lanes.index((i + 1) % 4).index(3) == 1)
        );
    }
    
    if accident {
        vec!['Y', 'E', 'S', '\n']
    } else {
        vec!['N', 'O', '\n']
    }
}
// </vc-code>


}

fn main() {}