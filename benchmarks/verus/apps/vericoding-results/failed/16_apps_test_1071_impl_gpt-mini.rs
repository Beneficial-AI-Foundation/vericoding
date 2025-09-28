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
/* helper modified by LLM (iteration 5): lemma that appending one element preserves sum relation */
fn sum_seq_snoc(prefix: Seq<int>, x: int)
    decreases prefix.len()
    ensures
        sum_seq(prefix + seq![x]) == sum_seq(prefix) + x,
{
    if prefix.len() == 0 {
        // base case: sum_seq(seq![x]) == x and sum_seq([]) == 0
    } else {
        sum_seq_snoc(prefix.drop_first(), x);
    }
}

/* helper modified by LLM (iteration 5): compute sum of Vec<i8> and relate it to spec sum_seq */
fn sum_vec(v: &Vec<i8>) -> i64
    requires
        forall|k: int| 0 <= k < v@.len() ==> v@[k] >= 0,
    ensures
        result as int == sum_seq(v@.map(|i: int, x: i8| x as int)),
{
    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            total as int == sum_seq(v@.slice(0, i as int).map(|j: int, x: i8| x as int)),
        decreases
            v.len() - i
    {
        let old_i = i;
        let vi: i64 = v[old_i] as i64;
        total = total + vi;
        i = i + 1;
        proof {
            assert(old_i < v.len());
            sum_seq_snoc(v@.slice(0, old_i as int).map(|j: int, x: i8| x as int), v@[old_i as int] as int);
            assert(total as int == sum_seq(v@.slice(0, old_i as int).map(|j: int, x: i8| x as int)) + (v@[old_i as int] as int));
            assert(total as int == sum_seq(v@.slice(0, i as int).map(|j: int, x: i8| x as int)));
        }
    }
    total
}

/* helper modified by LLM (iteration 5): compute shelves needed (i64) and relate to spec shelves_needed */
fn shelves_from_total(total: i64, capacity: i64) -> i64
    requires
        total >= 0,
        capacity > 0,
    ensures
        result as int == shelves_needed(total as int, capacity as int),
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
    /* code modified by LLM (iteration 5): compute totals and check capacity using helper functions */
    let total_cups: i64 = sum_vec(&a);
    let total_medals: i64 = sum_vec(&b);
    let shelves_cups: i64 = shelves_from_total(total_cups, 5);
    let shelves_medals: i64 = shelves_from_total(total_medals, 10);
    let n_i64: i64 = n as i64;
    let ok: bool = if shelves_cups > n_i64 { false } else { shelves_medals <= n_i64 - shelves_cups };
    let result = if ok { "YES".to_string() } else { "NO".to_string() };
    proof {
        assert(total_cups as int == sum_seq(a@.map(|i: int, x: i8| x as int)));
        assert(total_medals as int == sum_seq(b@.map(|i: int, x: i8| x as int)));
        assert(shelves_cups as int == shelves_needed(total_cups as int, 5));
        assert(shelves_medals as int == shelves_needed(total_medals as int, 10));
        assert(ok == (shelves_needed(total_cups as int, 5) + shelves_needed(total_medals as int, 10) <= n as int));
        if ok {
            assert(result@ == "YES"@);
        } else {
            assert(result@ == "NO"@);
        }
    }
    result
}
// </vc-code>


}

fn main() {}