// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines_spec(input);
    lines.len() >= 1 && 
    split_whitespace_spec(lines[0]).len() >= 2 &&
    {
        let n = parse_int_spec(split_whitespace_spec(lines[0])[0]);
        let k = parse_int_spec(split_whitespace_spec(lines[0])[1]);
        n > 0 && k > 0 && lines.len() >= n + 1 &&
        (forall|i: int| 1 <= i <= n ==> 
            i < lines.len() && split_whitespace_spec(lines[i]).len() >= 2)
    }
}

spec fn optimal_segment_profit(input: Seq<char>, n: nat, k: int) -> int {
    let lines = split_lines_spec(input);
    let difficulties = Seq::new(n, |i: int| 
        parse_int_spec(split_whitespace_spec(lines[i + 1])[0]));
    let costs = Seq::new(n, |i: int| 
        parse_int_spec(split_whitespace_spec(lines[i + 1])[1]));

    max_subsegment_profit(difficulties, costs, k)
}

spec fn max_subsegment_profit(difficulties: Seq<int>, costs: Seq<int>, k: int) -> int {
    if difficulties.len() == 0 {
        0
    } else {
        let all_segment_profits = Seq::new(difficulties.len(), |l: int| 
            Seq::new((difficulties.len() - l) as nat, |len: int|
                subsegment_profit(difficulties, costs, k, l as nat, (l + len) as nat)));
        max_value(0, max_in_nested_seq(all_segment_profits))
    }
}

spec fn subsegment_profit(difficulties: Seq<int>, costs: Seq<int>, k: int, l: nat, r: nat) -> int {
    let length = r - l + 1;
    let revenue = length * k;
    let cost_sum = sum_range(costs, l, r);
    let gap = if l == r { 0 } else { max_gap_squared(difficulties, l, r) };
    revenue - cost_sum - gap
}

spec fn split_lines_spec(s: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn split_whitespace_spec(s: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}

spec fn parse_int_spec(s: Seq<char>) -> int {
    0
}

spec fn int_to_string_result(n: int) -> Seq<char> {
    seq!['0']
}

spec fn sum_range(costs: Seq<int>, l: nat, r: nat) -> int {
    0
}

spec fn max_gap_squared(difficulties: Seq<int>, l: nat, r: nat) -> int {
    0
}

spec fn max_value(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn max_in_nested_seq(nested: Seq<Seq<int>>) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires
        input@.len() > 0,
    ensures
        result@.len() > 0,
        result@.last() == '\n',
        ({
            let lines = split_lines_spec(input@);
            (lines.len() == 0 || lines.len() == 1 || 
             split_whitespace_spec(lines[0]).len() < 2 ||
             parse_int_spec(split_whitespace_spec(lines[0])[0]) <= 0) ==> 
            result@ == "0\n"@
        }),
        (valid_input(input@) ==> {
            let lines = split_lines_spec(input@);
            let n = parse_int_spec(split_whitespace_spec(lines[0])[0]);
            let k = parse_int_spec(split_whitespace_spec(lines[0])[1]);
            exists|profit: int| 
                profit >= 0 && 
                result@ == int_to_string_result(profit) + "\n"@ &&
                profit == optimal_segment_profit(input@, n as nat, k)
        }),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}