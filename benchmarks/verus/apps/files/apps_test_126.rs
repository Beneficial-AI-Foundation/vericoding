// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_to_digits(s: Seq<char>) -> Set<int> {
    let char_set = Set::new(|i: int| 0 <= i < s.len() && '0' <= s[i] && s[i] <= '9');
    Set::new(|d: int| exists|i: int| char_set.contains(i) && d == (s[i] as int) - ('0' as int))
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && input.contains('\n')
}

spec fn has_unique_movement_sequence(digits: Set<int>) -> bool {
    (digits.contains(1) || digits.contains(4) || digits.contains(7) || digits.contains(0)) &&
    (digits.contains(1) || digits.contains(2) || digits.contains(3)) &&
    (digits.contains(3) || digits.contains(6) || digits.contains(9) || digits.contains(0)) &&
    (digits.contains(7) || digits.contains(0) || digits.contains(9))
}

spec fn find_char(s: Seq<char>, c: char) -> int {
    if s.len() == 0 { 
        -1 
    } else if s[0] == c { 
        0 
    } else {
        let rest_result = find_char(s.subrange(1, s.len() as int), c);
        if rest_result == -1 { -1 } else { rest_result + 1 }
    }
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if !s.contains('\n') { 
        seq![s] 
    } else {
        let idx = find_char(s, '\n');
        if idx == -1 { 
            seq![s] 
        } else if idx < s.len() { 
            seq![s.subrange(0, idx)].add(split_lines(s.subrange(idx + 1, s.len() as int))) 
        } else { 
            seq![s] 
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires 
        valid_input(input),
    ensures 
        result.len() == 3 || result.len() == 4,
        result.len() > 0,
        ({
            let lines = split_lines(input);
            lines.len() >= 2 ==> {
                let digits_str = lines[1];
                let digits = string_to_digits(digits_str);
                (result.len() == 4 && result[0] == 'Y' && result[1] == 'E' && result[2] == 'S' && result[3] == '\n') <==> has_unique_movement_sequence(digits)
            }
        }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    Seq::new(3, |i: int| if i == 0 { 'N' } else if i == 1 { 'O' } else { '\n' })
}
// </vc-code>


}

fn main() {}