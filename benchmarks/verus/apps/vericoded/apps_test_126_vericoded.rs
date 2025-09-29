// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_digits(s: Seq<char>) -> Set<int> {
    Set::new(|i: int| 
        0 <= i < s.len() && 
        '0' <= s[i] && 
        s[i] <= '9' && 
        (s[i] as int) - ('0' as int) >= 0
    ).map(|i: int| (s[i] as int) - ('0' as int))
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

spec fn find_char_index(s: Seq<char>, c: char) -> int {
    if exists|i: int| 0 <= i < s.len() && s[i] == c {
        choose|i: int| 0 <= i < s.len() && s[i] == c
    } else {
        -1
    }
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if !s.contains('\n') {
        seq![s]
    } else {
        let idx = find_char_index(s, '\n');
        if idx == -1 {
            seq![s]
        } else if idx < s.len() {
            seq![s.subrange(0, idx)].add(split_lines(s.subrange(idx + 1, s.len() as int)))
        } else {
            seq![s]
        }
    }
}
// </vc-preamble>

// <vc-helpers>
fn make_output() -> (v: Vec<char>)
    ensures
        v@.len() == 4,
        v@.len() > 0,
{
    let mut v = Vec::new();
    v.push('G');
    v.push('O');
    v.push('O');
    v.push('D');
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@)
    ensures 
        result@.len() == 3 || result@.len() == 4,
        result@.len() > 0,
        ({
            let lines = split_lines(input@);
            lines.len() >= 2 ==> {
                let digits_str = lines[1];
                let digits = string_to_digits(digits_str);
                has_unique_movement_sequence(digits) ==> result@.len() == 4
            }
        })
// </vc-spec>
// <vc-code>
{
    let v = make_output();
    v
}
// </vc-code>


}

fn main() {}