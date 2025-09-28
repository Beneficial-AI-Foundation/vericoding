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
    recommends m >= 1, i >= 0, s >= 0
{
    if i >= a.len() { 0 }
    else { (s + a[i]) / m }
}

spec fn compute_next_state(a: Seq<int>, m: int, i: int, s: int) -> int
    recommends m >= 1, i >= 0, s >= 0
{
    if i >= a.len() { s }
    else { (s + a[i]) % m }
}

spec fn correct_page_turns(result: Seq<int>, a: Seq<int>, m: int) -> bool
    recommends m >= 1
{
    result.len() == a.len() &&
    (forall|i: int| 0 <= i < a.len() ==> {
        let s = compute_state_at(a, m, i);
        #[trigger] result[i] == (s + a[i]) / m
    })
}

spec fn compute_state_at(a: Seq<int>, m: int, day: int) -> int
    recommends m >= 1, day >= 0
    decreases day
{
    if day <= 0 { 0 }
    else if day > a.len() { compute_state_at(a, m, a.len() as int) }
    else if day > 0 && day <= a.len() { (compute_state_at(a, m, day - 1) + a[day - 1]) % m }
    else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: Vec<i8>)
requires
    valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int))
ensures
    valid_output(result@.map(|i: int, x: i8| x as int), n as int),
    correct_page_turns(result@.map(|i: int, x: i8| x as int), a@.map(|i: int, x: i8| x as int), m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by ensuring all arguments passed to `a@.map` lambda functions are of type `int` when used with Verus `int` types, as `idx: int` and `x: int` are ghost. */
    let mut result: Vec<i8> = Vec::new();
    let mut s: i8 = 0; // s represents the current state (remains a non-negative residue modulo m)
    let mut i: i8 = 0; // i is the loop counter, representing the current day

    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            result.len() == i as int,
            result@.map(|k: int, x: i8| x as int).len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k] >= 0,
            s as int == compute_state_at(a@.map(|idx: int, x: i8| x as int), m as int, i as int),
            m >= 1
    {
        let ghost ghost_i = i as int;
        let ghost ghost_m = m as int;
        let ghost ghost_s = s as int;

        proof {
            if ghost_i < a@.len() {
                // This lemma is not defined, we need to assert the property directly for now.
                // We need to define lemma_compute_state_at_inductive to make this work
                // lemma_compute_state_at_inductive(a@.map(|idx: int, x: i8| x as int), m as int, i as int);
            }
        }

        let page_turns: i8 = compute_page_turns(a@.map(|idx: int, x: int| x), ghost_m, ghost_i, ghost_s) as i8;
        result.push(page_turns);

        s = compute_next_state(a@.map(|idx: int, x: int| x), ghost_m, ghost_i, ghost_s) as i8;
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}