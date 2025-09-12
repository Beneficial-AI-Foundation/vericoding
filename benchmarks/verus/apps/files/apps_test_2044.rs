// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n >= 1 && m >= 1 && a.len() == n && 
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 1)
}

spec fn valid_output(result: Seq<int>, n: int) -> bool {
    result.len() == n && (forall|i: int| 0 <= i < result.len() ==> result[i] >= 0)
}

spec fn compute_page_turns(a: Seq<int>, m: int, i: int, s: int) -> int
    requires m >= 1 && i >= 0 && s >= 0
{
    if i >= a.len() { 0 }
    else { (s + a[i]) / m }
}

spec fn compute_next_state(a: Seq<int>, m: int, i: int, s: int) -> int
    requires m >= 1 && i >= 0 && s >= 0
{
    if i >= a.len() { s }
    else { (s + a[i]) % m }
}

spec fn correct_page_turns(result: Seq<int>, a: Seq<int>, m: int) -> bool
    requires m >= 1
{
    result.len() == a.len() &&
    (forall|i: int| 0 <= i < a.len() ==> {
        let s = compute_state_at(a, m, i);
        result[i] == (s + a[i]) / m
    })
}

spec fn compute_state_at(a: Seq<int>, m: int, day: int) -> int
    requires m >= 1 && day >= 0
    decreases day
{
    if day == 0 { 0 }
    else if day > a.len() { compute_state_at(a, m, a.len()) }
    else { (compute_state_at(a, m, day - 1) + a[day - 1]) % m }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, a: Seq<int>) -> (result: Seq<int>)
    requires
        valid_input(n, m, a),
    ensures
        valid_output(result, n),
        correct_page_turns(result, a, m),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}