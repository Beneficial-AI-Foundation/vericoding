// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn all_distances_equal(positions: Seq<int>) -> bool {
    if positions.len() <= 2 {
        true
    } else {
        let first_dist = positions[1] - positions[0];
        true /* simplified to avoid trigger issues */
    }
}

spec fn count_visits(visits: Seq<int>, stop: int) -> int {
    0 /* placeholder implementation */
}

spec fn max_val(s: Seq<int>) -> int {
    0 /* placeholder implementation */
}

spec fn sum(s: Seq<int>) -> int {
    0 /* placeholder implementation */
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn compute_counts(n: int, visits: Seq<int>) -> Seq<int> {
    let base_counts = Seq::new(n as nat, |i: int| count_visits(visits, i + 1));
    Seq::new(n as nat, |i: int| 
        if i == 0 || i == n - 1 { 
            base_counts[i] * 2 
        } else { 
            base_counts[i] 
        }
    )
}

spec fn compute_max_rounds(counts: Seq<int>) -> int {
    max_val(Seq::new(counts.len(), |i: int| counts[i] / 2))
}

spec fn has_ambiguous_path(n: int, positions: Seq<int>, visits: Seq<int>) -> bool {
    let counts = compute_counts(n, visits);
    let max_rounds = compute_max_rounds(counts);
    let remaining_counts = Seq::new(n as nat, |i: int| counts[i] - max_rounds * 2);
    let all_zero = forall|i: int| 0 <= i < n ==> #[trigger] remaining_counts[i] == 0;

    all_zero && n > 2 && !all_distances_equal(positions)
}

spec fn calculate_total_distance(n: int, positions: Seq<int>, visits: Seq<int>) -> int {
    let counts = compute_counts(n, visits);
    let max_rounds = compute_max_rounds(counts);
    let remaining_counts = Seq::new(n as nat, |i: int| counts[i] - max_rounds * 2);
    let all_zero = forall|i: int| 0 <= i < n ==> #[trigger] remaining_counts[i] == 0;

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
/* helper modified by LLM (iteration 5): Removed duplicate helper definitions as they are already defined in the preamble */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, positions: Vec<i8>, m: i8, visits: Vec<i8>) -> (result: i8)
    requires
        n >= 1,
        positions.len() == n as nat,
        is_sorted(positions@.map(|i, x: i8| x as int)),
        m >= 1,
        visits.len() == m as nat
    ensures
        result as int == if has_ambiguous_path(n as int, positions@.map(|i, x: i8| x as int), visits@.map(|i, x: i8| x as int)) {
            -1
        } else {
            calculate_total_distance(n as int, positions@.map(|i, x: i8| x as int), visits@.map(|i, x: i8| x as int))
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed erroneous uses of `verus_macro_common` to fix compilation. Changed `has_ambiguous` condition to use `all_zero_spec` directly, and implicitly handle a `total_distance` calculation when not ambiguous. */
{
    let ghost positions_int: Seq<int> = positions@.map(|i, x: i8| x as int);
    let ghost visits_int: Seq<int> = visits@.map(|i, x: i8| x as int);
    let ghost n_int: int = n as int;

    let ghost counts_spec = compute_counts(n_int, visits_int);
    let ghost max_rounds_spec = compute_max_rounds(counts_spec);
    let ghost remaining_counts_spec = Seq::new(n_int as nat, |i: int| counts_spec[i] - max_rounds_spec * 2);
    let ghost all_zero_spec = forall|i: int| 0 <= i < n_int ==> remaining_counts_spec[i] == 0;
    let ghost all_distances_equal_spec = if n_int <= 2 {
        true
    } else {
        let first_dist = positions_int@[1] - positions_int@[0];
        forall|i: int| 0 <= i < n_int - 1 ==> (positions_int@[i+1] - positions_int@[i]) == first_dist
    };

    let ghost has_ambiguous: bool = all_zero_spec && n_int > 2 && !all_distances_equal_spec;

    if has_ambiguous {
        return -1i8;
    }

    let ghost total_distance: int;
    if all_zero_spec {
        if n_int == 2 {
            total_distance = max_rounds_spec * (positions_int@[1] - positions_int@[0]) * 2 - (positions_int@[1] - positions_int@[0]);
        } else {
            let first_dist: int = positions_int@[1] - positions_int@[0];
            total_distance = max_rounds_spec * first_dist * 2 * (n_int - 1) - first_dist;
        }
    } else {
        let ghost edge_distance_sum: int = (0..n_int as nat -1).fold(0, |acc: int, i: nat| {
            acc + min(remaining_counts_spec@[i as int], remaining_counts_spec@[i as int + 1]) * (positions_int@[i as int + 1] - positions_int@[i as int])
        });
        let ghost total_edge_length_sum: int = (0..n_int as nat -1).fold(0, |acc: int, i: nat| {
            acc + (positions_int@[i as int + 1] - positions_int@[i as int])
        });
        total_distance = edge_distance_sum + max_rounds_spec * 2 * total_edge_length_sum;
    }

    total_distance as i8
}
// </vc-code>


}

fn main() {}