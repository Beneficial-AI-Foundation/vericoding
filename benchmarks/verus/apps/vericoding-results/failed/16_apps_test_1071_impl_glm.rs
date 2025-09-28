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

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>, b: Vec<i8>, n: i8) -> (result: String)
    requires valid_input(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int)
    ensures result@ == (if can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int) { "YES"@ } else { "NO"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed missing result variable by assigning to named return parameter */
    let mut total_cups: i64 = 0;
    for i in 0..a.len() {
        total_cups += a[i] as i64;
    }

    let mut total_medals: i64 = 0;
    for i in 0..b.len() {
        total_medals += b[i] as i64;
    }

    let shelves_cups: i64 = if total_cups == 0 { 0 } else { (total_cups - 1) / 5 + 1 };
    let shelves_medals: i64 = if total_medals == 0 { 0 } else { (total_medals - 1) / 10 + 1 };

    let can_place = shelves_cups + shelves_medals <= n as i64;

    proof {
        assert(total_cups as int == sum_seq(a@.map(|i: int, x: i8| x as int)));
        assert(total_medals as int == sum_seq(b@.map(|i: int, x: i8| x as int)));
        assert(shelves_cups as int == shelves_needed(total_cups as int, 5));
        assert(shelves_medals as int == shelves_needed(total_medals as int, 10));
        assert((shelves_cups + shelves_medals) as int == shelves_cups as int + shelves_medals as int);
        assert(can_place == (shelves_cups as int + shelves_medals as int <= n as int));
        assert(can_place == can_place_all(a@.map(|i: int, x: i8| x as int), b@.map(|i: int, x: i8| x as int), n as int));
    }

    if can_place {
        result = String::from("YES");
    } else {
        result = String::from("NO");
    }
    result
}
// </vc-code>


}

fn main() {}