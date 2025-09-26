// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: int, a: Seq<int>) -> bool {
    n >= 1 && n <= 3000 &&
    s >= 1 && s <= 3000 &&
    a.len() == n &&
    forall|i: int| 0 <= i < n ==> a[i] >= 1 && a[i] <= 3000
}

spec fn compute_subset_sum_ways(n: int, s: int, a: Seq<int>) -> int {
    let dp = compute_dp_table(n, s, a);
    if dp.len() > n && dp[n].len() > s { dp[n][s] } else { 0 }
}

spec fn compute_dp_table(n: int, s: int, a: Seq<int>) -> Seq<Seq<int>>
    decreases n
{
    if n == 1 {
        let base = Seq::new(s+1, |j: int| if j == 0 { 1 } else { 0 });
        let new_row = Seq::new(s+1, |j: int| {
            let doubled = (base[j] * 2) % 998244353;
            if j >= a[0] && j - a[0] >= 0 && j - a[0] < s+1 { 
                (doubled + base[j - a[0]]) % 998244353
            } else { 
                doubled
            }
        });
        seq![base, new_row]
    } else {
        let prev_dp = compute_dp_table(n-1, s, a.subrange(0, n-1));
        let new_row = Seq::new(s+1, |j: int| {
            let doubled = (prev_dp[n-1][j] * 2) % 998244353;
            if j >= a[n-1] && j - a[n-1] >= 0 && j - a[n-1] < s+1 {
                (doubled + prev_dp[n-1][j - a[n-1]]) % 998244353
            } else {
                doubled
            }
        });
        prev_dp.push(new_row)
    }
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq![], seq![]]
}

spec fn split_whitespace(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq![]]
}

spec fn string_to_int(s: Seq<char>) -> int {
    0
}

spec fn int_to_string(n: int) -> Seq<char> {
    seq!['0']
}

spec fn valid_parsed_input(input: Seq<char>, n: int, s: int, a: Seq<int>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 2 && {
        let first_line = split_whitespace(lines[0]);
        let second_line = split_whitespace(lines[1]);
        first_line.len() >= 2 && second_line.len() == n &&
        n == string_to_int(first_line[0]) &&
        s == string_to_int(first_line[1]) &&
        a.len() == n &&
        (forall|i: int| 0 <= i < n ==> (a[i] == string_to_int(second_line[i]))) &&
        valid_input(n, s, a)
    }
}

spec fn valid_parsed_input_exists(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    if lines.len() < 2 {
        false
    } else {
        let first_line = split_whitespace(lines[0]);
        let second_line = split_whitespace(lines[1]);
        if first_line.len() < 2 || second_line.len() == 0 {
            false
        } else {
            let n = string_to_int(first_line[0]);
            let s = string_to_int(first_line[1]);
            n >= 1 && n <= 3000 && s >= 1 && s <= 3000 && second_line.len() == n &&
            forall|i: int| 0 <= i < n ==> {
                let ai = string_to_int(second_line[i]);
                ai >= 1 && ai <= 3000
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires
        stdin_input.len() > 0,
    ensures
        result.len() > 0,
    ensures
        result.as_bytes()[result.len()-1] == 10u8
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "0\n".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {}