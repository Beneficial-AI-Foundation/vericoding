use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::calc;

proof fn lemma_difference_sum_cubes_and_sum_numbers(n: u32)
    requires n >= 0
    ensures (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 == (n * (n + 1) / 2) * (n * (n + 1) / 2 - 1)
{
    let a = n * (n + 1);
    assert(a % 2 == 0);
    let k = a / 2;
    calc! {
        (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
        == { rewrite (n * n * (n + 1) * (n + 1)) == a * a; }
        (a * a) / 4 - a / 2;
        == { rewrite (a * a) / 4 - a / 2 == (a * a - 2 * a) / 4; }
        (a * a - 2 * a) / 4;
        == { rewrite a * a - 2 * a == a * (a - 2); }
        (a * (a - 2)) / 4;
        == { rewrite a == 2 * k; }
        (2 * k * (2 * k - 2)) / 4;
        == { rewrite 2 * k - 2 == 2 * (k - 1); }
        (2 * k * 2 * (k - 1)) / 4;
        == { rewrite 2 * 2 == 4; }
        (4 * k * (k - 1)) / 4;
        == { rewrite (4 * k * (k - 1)) / 4 == k * (k - 1); }
        k * (k - 1);
        == { rewrite k == a / 2; }
        (a / 2) * (a / 2 - 1);
        == { rewrite a == n * (n + 1); }
        (n * (n + 1) / 2) * (n * (n + 1) / 2 - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    let a = n * (n + 1) / 2;
    let diff = a * (a - 1);
    proof {
        lemma_difference_sum_cubes_and_sum_numbers(n);
    }
    diff
}
// </vc-code>

fn main() {}

}