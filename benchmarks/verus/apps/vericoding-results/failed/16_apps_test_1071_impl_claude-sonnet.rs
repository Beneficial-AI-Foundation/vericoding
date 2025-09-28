// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>, b: Seq<int>, n: int) -> bool {
    a.len() >= 0 && b.len() >= 0 &&
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 0) &&
    (forall|j: int| 0 <= j < b.len() ==> b[j] >= 0) &&
    n >= 1
}

spec fn sum_seq(s: Seq<int>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.drop_first()) }
}

spec fn shelves_needed(total: int, capacity: int) -> int
    recommends capacity > 0
{
    if total == 0 { 0 } else { (total - 1) / capacity + 1 }
}

spec fn can_place_all(a: Seq<int>, b: Seq<int>, n: int) -> bool
    recommends valid_input(a, b, n)
{
    let total_cups = sum_seq(a);
    let total_medals = sum_seq(b);
    let shelves_for_cups = shelves_needed(total_cups, 5);
    let shelves_for_medals = shelves_needed(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added length and value bounds to match solve function requirements */
fn compute_sum(v: Vec<i8>) -> (result: i32)
    requires 
        forall|i: int| 0 <= i < v@.len() ==> v@[i] >= 0,
        v@.len() <= 1000,
        forall|i: int| 0 <= i < v@.len() ==> v@[i] <= 100
    ensures result as int == sum_seq(v@.map(|i: int, x: i8| x as int))
{
    let mut sum = 0i32;
    let mut idx = 0usize;
    
    while idx < v.len()
        invariant
            0 <= idx <= v@.len(),
            sum as int == sum_seq(v@.subrange(0, idx as int).map(|i: int, x: i8| x as int)),
            forall|i: int| 0 <= i < v@.len() ==> v@[i] >= 0,
            forall|i: int| 0 <= i < v@.len() ==> v@[i] <= 100,
            sum >= 0,
            sum <= (idx as int) * 100
        decreases v@.len() - idx
    {
        proof {
            assert(v@[idx as int] >= 0);
            assert(v@[idx as int] <= 100);
            assert(sum + (v@[idx as int] as int) <= (idx as int) * 100 + 100);
            assert((idx as int) * 100 + 100 == ((idx + 1) as int) * 100);
        }
        sum = sum + (v[idx] as i32);
        idx = idx + 1;
    }
    
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    
    sum
}

fn compute_shelves_needed(total: i32, capacity: i32) -> (result: i32)
    requires 
        capacity > 0,
        total >= 0
    ensures result as int == shelves_needed(total as int, capacity as int)
{
    if total == 0 {
        0
    } else {
        (total - 1) / capacity + 1
    }
}

lemma lemma_valid_input_implies_bounds(a: Vec<i8>, b: Vec<i8>, n: i8)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures 
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= 0,
        forall|i: int| 0 <= i < b@.len() ==> b@[i] >= 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= 100,
        forall|i: int| 0 <= i < b@.len() ==> b@[i] <= 100,
        a@.len() <= 1000,
        b@.len() <= 1000
{
    assert(forall|i: int| 0 <= i < a@.len() ==> a@.map(|j: int, x: i8| x as int)[i] >= 0);
    assert(forall|i: int| 0 <= i < b@.len() ==> b@.map(|j: int, x: i8| x as int)[i] >= 0);
    assert(forall|i: int| 0 <= i < a@.len() ==> a@[i] >= 0);
    assert(forall|i: int| 0 <= i < b@.len() ==> b@[i] >= 0);
    assert(forall|i: int| 0 <= i < a@.len() ==> a@[i] <= 127);
    assert(forall|i: int| 0 <= i < b@.len() ==> b@[i] <= 127);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>, b: Vec<i8>, n: i8) -> (result: String)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures result@ == (if can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int) { "YES"@ } else { "NO"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed manual validation and used lemma to establish bounds */
    
    proof {
        lemma_valid_input_implies_bounds(a, b, n);
    }
    
    let total_cups = compute_sum(a);
    let total_medals = compute_sum(b);
    
    let shelves_for_cups = compute_shelves_needed(total_cups, 5);
    let shelves_for_medals = compute_shelves_needed(total_medals, 10);
    
    if shelves_for_cups + shelves_for_medals <= (n as i32) {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}