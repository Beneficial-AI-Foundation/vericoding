// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_company_input(input: &str) -> bool {
    let lines = split_lines_func(input);
    lines.len() >= 1 && 
    is_valid_positive_int(lines.index(0)) &&
    {
        let n = parse_int_func(lines.index(0));
        n >= 1 && lines.len() >= n + 1 &&
        (forall|i: int| 1 <= i <= n ==> valid_company_line(lines.index(i)))
    }
}

spec fn valid_company_line(line: &str) -> bool {
    let parts = split_spaces_func(line);
    parts.len() >= 1 && is_valid_positive_int(parts.index(0)) &&
    {
        let m = parse_int_func(parts.index(0));
        m >= 1 && parts.len() == m + 1 &&
        (forall|j: int| 1 <= j <= m ==> is_valid_positive_int(parts.index(j)))
    }
}

spec fn is_valid_positive_int(s: &str) -> bool {
    s.len() >= 1 && (forall|i: int| 0 <= i < s.len() ==> '0' <= s.as_bytes().index(i) as char <= '9')
}

spec fn parse_companies(input: &str) -> Seq<Seq<int>> {
    let lines = split_lines_func(input);
    let n = parse_int_func(lines.index(0));
    Seq::new(n as nat, |i: int| {
        let parts = split_spaces_func(lines.index(i + 1));
        let m = parse_int_func(parts.index(0));
        Seq::new(m as nat, |j: int| parse_int_func(parts.index(j + 1)))
    })
}

spec fn calculate_minimum_increase(companies: Seq<Seq<int>>) -> int {
    let global_max = global_max_salary(companies);
    sum_over_companies(companies, global_max)
}

spec fn global_max_salary(companies: Seq<Seq<int>>) -> int {
    max_in_seq_of_seq(Seq::new(companies.len(), |i: int| max_in_seq_func(companies.index(i))))
}

spec fn sum_over_companies(companies: Seq<Seq<int>>, global_max: int) -> int
    decreases companies.len()
{
    if companies.len() == 1 {
        let company_max = max_in_seq_func(companies.index(0));
        let increase_per_employee = global_max - company_max;
        increase_per_employee * companies.index(0).len()
    } else {
        let company_max = max_in_seq_func(companies.index(0));
        let increase_per_employee = global_max - company_max;
        increase_per_employee * companies.index(0).len() + sum_over_companies(companies.subrange(1, companies.len() as int), global_max)
    }
}

spec fn max_in_seq_func(s: Seq<int>) -> int {
    max_in_seq(s)
}

spec fn max_in_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        s.index(0)
    } else if s.index(0) >= max_in_seq(s.subrange(1, s.len() as int)) {
        s.index(0)
    } else {
        max_in_seq(s.subrange(1, s.len() as int))
    }
}

spec fn max_in_seq_of_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        s.index(0)
    } else if s.index(0) >= max_in_seq_of_seq(s.subrange(1, s.len() as int)) {
        s.index(0)
    } else {
        max_in_seq_of_seq(s.subrange(1, s.len() as int))
    }
}

spec fn split_lines_func(s: &str) -> Seq<&str> {
    Seq::empty()
}

spec fn split_spaces_func(s: &str) -> Seq<&str> {
    Seq::empty()
}

spec fn parse_int_func(s: &str) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: int)
    requires
        input.len() > 0,
        valid_company_input(input),
    ensures
        result >= 0,
        result == calculate_minimum_increase(parse_companies(input)),
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