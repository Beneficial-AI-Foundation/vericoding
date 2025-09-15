// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn all_distances_equal(positions: Seq<int>) -> bool 
    recommends 
        positions.len() >= 2,
        forall|i: int| 0 <= i < positions.len() - 1 ==> positions[i] < positions[i + 1]
{
    if positions.len() <= 2 { 
        true 
    } else {
        let first_dist = positions[1] - positions[0];
        forall|i: int| 1 <= i < positions.len() - 1 ==> positions[i + 1] - positions[i] == first_dist
    }
}

spec fn count_visits(visits: Seq<int>, target: int) -> int {
    visits.filter(|x: int| x == target).len() as int
}

spec fn compute_counts(n: int, visits: Seq<int>) -> Seq<int> 
    recommends 
        n >= 2,
        forall|i: int| 0 <= i < visits.len() ==> 1 <= visits[i] <= n
{
    let base_counts = Seq::new(n as nat, |i: int| count_visits(visits, i + 1));
    Seq::new(n as nat, |i: int| 
        if i == 0 || i == n - 1 { 
            base_counts[i] * 2 
        } else { 
            base_counts[i] 
        }
    )
}

spec fn max_val(s: Seq<int>) -> int {
    if s.len() == 0 {
        0
    } else {
        s.fold_left(s[0], |acc: int, x: int| if acc >= x { acc } else { x })
    }
}

spec fn compute_max_rounds(counts: Seq<int>) -> int 
    recommends counts.len() > 0
{
    max_val(Seq::new(counts.len(), |i: int| counts[i] / 2))
}

spec fn has_ambiguous_path(n: int, positions: Seq<int>, visits: Seq<int>) -> bool
    recommends 
        n >= 2,
        positions.len() == n,
        forall|i: int| 0 <= i < visits.len() ==> 1 <= visits[i] <= n,
        forall|i: int| 0 <= i < n - 1 ==> positions[i] < positions[i + 1]
{
    let counts = compute_counts(n, visits);
    let max_rounds = compute_max_rounds(counts);
    let remaining_counts = Seq::new(n as nat, |i: int| counts[i] - max_rounds * 2);
    let all_zero = forall|i: int| 0 <= i < n ==> remaining_counts[i] == 0;

    all_zero && n > 2 && !all_distances_equal(positions)
}

spec fn sum(s: Seq<int>) -> int {
    s.fold_left(0, |acc: int, x: int| acc + x)
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn calculate_total_distance(n: int, positions: Seq<int>, visits: Seq<int>) -> int
    recommends 
        n >= 2,
        positions.len() == n,
        forall|i: int| 0 <= i < visits.len() ==> 1 <= visits[i] <= n,
        forall|i: int| 0 <= i < n - 1 ==> positions[i] < positions[i + 1],
        !has_ambiguous_path(n, positions, visits),
        visits.len() >= 1
{
    let counts = compute_counts(n, visits);
    let max_rounds = compute_max_rounds(counts);
    let remaining_counts = Seq::new(n as nat, |i: int| counts[i] - max_rounds * 2);
    let all_zero = forall|i: int| 0 <= i < n ==> remaining_counts[i] == 0;

    if all_zero {
        if n == 2 {
            max_rounds * (positions[1] - positions[0]) * 2 - (positions[1] - positions[0])
        } else {
            let first_dist = positions[1] - positions[0];
            max_rounds * first_dist * 2 * (n - 1) - first_dist
        }
    } else {
        let edge_distance = sum(Seq::new((n-1) as nat, |i: int| min(remaining_counts[i], remaining_counts[i+1]) * (positions[i+1] - positions[i])));
        let total_edge_length = sum(Seq::new((n-1) as nat, |i: int| positions[i+1] - positions[i]));
        edge_distance + max_rounds * 2 * total_edge_length
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, positions: Seq<int>, m: int, visits: Seq<int>) -> (result: int)
    requires 
        n >= 2,
        positions.len() == n,
        m >= 1,
        visits.len() == m,
        forall|i: int| 0 <= i < visits.len() ==> 1 <= visits[i] <= n,
        forall|i: int| 0 <= i < n - 1 ==> positions[i] < positions[i + 1],
        forall|i: int| 0 <= i < positions.len() ==> positions[i] >= 1,
        is_sorted(visits)
    ensures 
        result >= -1,
        result == -1 <==> has_ambiguous_path(n, positions, visits),
        result >= 0 ==> result == calculate_total_distance(n, positions, visits),
        result >= 0 ==> (forall|i: int| 0 <= i < n-1 ==> positions[i+1] - positions[i] > 0)
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