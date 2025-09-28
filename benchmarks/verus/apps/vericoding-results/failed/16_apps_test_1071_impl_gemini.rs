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
/* helper modified by LLM (iteration 2): removed proof block to fix compilation error */
fn sum_vec(v: &Vec<i8>) -> (total: i32)
    requires
        forall|i: int| 0 <= i < v@.len() ==> v@[i] >= 0,
    ensures
        total as int == sum_seq(v@.map(|_idx: int, x: i8| x as int)),
        total >= 0,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum >= 0,
            sum as int == sum_seq(v@.take(i as int).map(|_idx: int, x: i8| x as int)),
        decreases v.len() - i
    {
        let val = v[i] as i32;
        sum = sum + val;
        i = i + 1;
    }
    sum
}

fn compute_shelves_needed(total: i32, capacity: i32) -> (shelves: i32)
    requires
        total >= 0,
        capacity > 0,
    ensures
        shelves == shelves_needed(total as int, capacity as int),
{
    if total == 0 {
        0
    } else {
        (total - 1) / capacity + 1
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>, b: Vec<i8>, n: i8) -> (result: String)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures result@ == (if can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int) { "YES"@ } else { "NO"@ })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): no logical change needed */
{
    let total_cups = sum_vec(&a);
    let total_medals = sum_vec(&b);
    let shelves_for_cups = compute_shelves_needed(total_cups, 5);
    let shelves_for_medals = compute_shelves_needed(total_medals, 10);
    if shelves_for_cups + shelves_for_medals <= (n as i32) {
        String::from_str("YES")
    } else {
        String::from_str("NO")
    }
}
// </vc-code>


}

fn main() {}