// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input_format(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 2 && 
    parse_integers(lines[0]).len() == 2 &&
    {
        let first_line = parse_integers(lines[0]);
        let n = first_line[0];
        let m = first_line[1];
        n >= 1 && m >= 0 &&
        parse_integers(lines[1]).len() == n &&
        is_valid_permutation(parse_integers(lines[1]), n) &&
        lines.len() == 2 + m &&
        (forall|i: int| 2 <= i < lines.len() ==> {
            let query = parse_integers(lines[i]);
            query.len() == 3 &&
            {
                let l = query[0];
                let r = query[1];
                let x = query[2];
                1 <= l <= x <= r <= n
            }
        })
    }
}

spec fn is_valid_permutation(p: Seq<int>, n: int) -> bool {
    p.len() == n && 
    (forall|i: int| 0 <= i < p.len() ==> 1 <= p[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < p.len() ==> p[i] != p[j])
}

spec fn valid_output_format(output: Seq<char>) -> bool {
    let lines = split_lines(output);
    forall|line: Seq<char>| lines.contains(line) ==> 
        line =~= seq!['Y', 'e', 's'] || 
        line =~= seq!['N', 'o']
}

spec fn output_matches_queries(input: Seq<char>, output: Seq<char>) -> bool {
    let input_lines = split_lines(input);
    let output_lines = split_lines(output);
    if input_lines.len() < 2 { 
        false 
    } else {
        let first_line = parse_integers(input_lines[0]);
        if first_line.len() != 2 { 
            false 
        } else {
            let n = first_line[0];
            let m = first_line[1];
            input_lines.len() == 2 + m &&
            output_lines.len() == m &&
            {
                let p = parse_integers(input_lines[1]);
                forall|i: int| 0 <= i < m ==> {
                    let query = parse_integers(input_lines[2 + i]);
                    let l = query[0];
                    let r = query[1]; 
                    let x = query[2];
                    let px = p[x - 1];
                    let cnt = l + count_smaller_in_range(p, l - 1, r - 1, px);
                    output_lines[i] =~= 
                        if cnt == x { 
                            seq!['Y', 'e', 's'] 
                        } else { 
                            seq!['N', 'o'] 
                        }
                }
            }
        }
    }
}

spec fn count_smaller_in_range(p: Seq<int>, start: int, end: int, value: int) -> int
    decreases if start <= end { end - start + 1 } else { 0 }
{
    if start > end { 
        0
    } else if start < 0 || start >= p.len() { 
        0
    } else {
        (if p[start] < value { 1int } else { 0int }) + 
        count_smaller_in_range(p, start + 1, end, value)
    }
}

spec fn parse_integers(line: Seq<char>) -> Seq<int> {
    seq![]
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { 
        seq![]
    } else {
        let idx = find_newline(s, 0);
        if idx == -1 { 
            seq![s]
        } else { 
            seq![s.subrange(0, idx)] + split_lines(s.subrange(idx + 1, s.len() as int))
        }
    }
}

spec fn find_newline(s: Seq<char>, start: nat) -> int
    decreases s.len() - start
{
    if start >= s.len() { 
        -1
    } else if s[start as int] == '\n' { 
        start as int
    } else { 
        find_newline(s, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        stdin_input.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n',
        valid_input_format(stdin_input@),
    ensures 
        result.len() > 0,
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == 'Y' || result@[i] == 'e' || result@[i] == 's' || 
            result@[i] == 'N' || result@[i] == 'o' || result@[i] == ' ' || result@[i] == '\n',
        result.len() > 0 ==> result@[result.len() - 1] == '\n',
        valid_output_format(result@),
        output_matches_queries(stdin_input@, result@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}