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
/* helper modified by LLM (iteration 5): Fixed map function usage and proof assertions */
fn total_cups(a: &Vec<i8>) -> (sum: u64)
    requires forall|i: int| 0 <= i < a@.len() ==> a@[i] >= 0
    ensures sum == sum_seq(a@)
{
    let mut s: u64 = 0;
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i <= n,
            n <= a@.len(),
            s as int == sum_seq(a@.subrange(0, i as int)),
            forall|j: int| i as int <= j < n as int ==> a@[j] >= 0
        decreases n - i
    {
        proof {
            assert(i < a@.len());
        }
        let x = a[i] as u64;
        s = s + x;
        i = i + 1;
    }
    s
}

fn total_medals(b: &Vec<i8>) -> (sum: u64)
    requires forall|i: int| 0 <= i < b@.len() ==> b@[i] >= 0
    ensures sum == sum_seq(b@)
{
    let mut s: u64 = 0;
    let mut i: usize = 0;
    let n = b.len();
    while i < n
        invariant
            0 <= i <= n,
            n <= b@.len(),
            s as int == sum_seq(b@.subrange(0, i as int)),
            forall|j: int| i as int <= j < n as int ==> b@[j] >= 0
        decreases n - i
    {
        proof {
            assert(i < b@.len());
        }
        let x = b[i] as u64;
        s = s + x;
        i = i + 1;
    }
    s
}

fn shelves_for_items(total: u64, capacity: u64) -> (count: u64)
    requires capacity > 0, total >= 0
    ensures count == shelves_needed(total as int, capacity as int)
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
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by working with Seq directly */
    let cups_total = total_cups(&a);
    let medals_total = total_medals(&b);
    let cups_shelves = shelves_for_items(cups_total, 5);
    let medals_shelves = shelves_for_items(medals_total, 10);
    let total_shelves = cups_shelves + medals_shelves;
    if total_shelves <= n as u64 {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}