// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_squares(p: int, a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        (p - a[0]) * (p - a[0]) + sum_squares(p, a.subrange(1, a.len() as int))
    }
}

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && n <= 100 && a.len() == n && 
    forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= -100 && #[trigger] a[i] <= 100
}

spec fn is_optimal_cost(result: int, a: Seq<int>) -> bool {
    result >= 0 &&
    exists|p: int| -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall|p: int| -100 <= p <= 100 ==> result <= sum_squares(p, a)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_squares_iterative(p: int, a: Seq<int>)
    ensures
        sum_squares(p, a) == {
            let mut sum = 0;
            let mut i = 0;
            while i < a.len()
                invariant
                    0 <= i <= a.len(),
                    sum == sum_squares(p, a.take(i)),
            {
                let diff = p - a[i];
                sum = sum + diff * diff;
                i = i + 1;
            }
            sum
        }
{
    if a.len() == 0 {
        assert(a.take(0).len() == 0);
        assert(sum_squares(p, a) == 0);
    } else {
        let a_rest = a.subrange(1, a.len() as int);
        let a_first = a[0];
        lemma_sum_squares_iterative(p, a_rest);
        assert(sum_squares(p, a) == (p - a_first) * (p - a_first) + sum_squares(p, a_rest));
        assert(a.take(1) == seq![a_first]);
        assert(a.take(a.len()) == a);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|_i: int, x: i8| x as int))
    ensures is_optimal_cost(result as int, a@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let a_mapped = a@.map(|_i: int, x: i8| x as int);
    let mut min_sum: int = 4000001;
    let mut best_p: int = -101;

    let mut p = -100;
    while p <= 100
        invariant
            best_p == -101 || (best_p >= -100 && best_p <= 100),
            best_p == -101 || min_sum == sum_squares(best_p, a_mapped),
            forall|prev_p: int| -100 <= prev_p < p ==> min_sum <= sum_squares(prev_p, a_mapped),
            min_sum >= 0,
        decreases 201 - (p + 100)
    {
        let mut current_sum: int = 0;
        let mut i = 0;
        while i < a_mapped.len()
            invariant
                0 <= i <= a_mapped.len(),
                current_sum == sum_squares(p, a_mapped.take(i)),
        {
            let diff = p - a_mapped[i];
            current_sum = current_sum + diff * diff;
            i = i + 1;
        }
        assert(current_sum == sum_squares(p, a_mapped));

        if best_p == -101 || current_sum < min_sum {
            min_sum = current_sum;
            best_p = p;
        }
        p = p + 1;
    }

    result = min_sum as i8;
}
// </vc-code>


}

fn main() {}