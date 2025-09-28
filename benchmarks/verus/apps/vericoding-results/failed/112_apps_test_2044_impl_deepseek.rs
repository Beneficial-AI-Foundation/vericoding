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

proof fn lemma_compute_state_at_next(a: Seq<int>, m: int, i: int)
    requires m >= 1, i >= 0, i < a.len()
    ensures compute_state_at(a, m, i + 1) == (compute_state_at(a, m, i) + a[i]) % m
{
    if i > 0 {
        lemma_compute_state_at_next(a, m, i - 1);
    }
}

proof fn lemma_page_turns_correct(a: Seq<int>, m: int, i: int)
    requires m >= 1, i >= 0, i < a.len()
    ensures compute_page_turns(a, m, i, compute_state_at(a, m, i)) == (compute_state_at(a, m, i) + a[i]) / m
{
    if i > 0 {
        lemma_compute_state_at_next(a, m, i - 1);
    }
}

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
    requires(n as int >= 1 && m as int >= 1 && a@.len() == n as int) by {
        assert(valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int)));
    }
    let mut result = Vec::new();
    let mut s: i8 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i,
            s as int == compute_state_at(a@.map(|_, x: i8| x as int), m as int, i as int),
            valid_output(result@.map(|_, x: i8| x as int), n as int),
            correct_page_turns(result@.map(|_, x: i8| x as int), a@.map(|_, x: i8| x as int), m as int) // Corrected the map function
        decreases a.len() - i
    {
        proof {
            lemma_page_turns_correct(a@.map(|_, x: i8| x as int), m as int, i as int);
        }
        let turns = (s + a[i]) / m;
        s = (s + a[i]) % m;
        result.push(turns);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}