// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
}

spec fn transform(a: Seq<int>) -> Seq<int> {
    Seq::new(a.len(), |i: int| a[i] - (i + 1))
}

spec fn sum_abs_diffs(a: Seq<int>, target: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        abs_int(a[0] - target) + sum_abs_diffs(a.subrange(1, a.len() as int), target)
    }
}

spec fn median_of(a: Seq<int>) -> int {
    let sorted = sorted_seq(a);
    if sorted.len() == 0 {
        0
    } else if sorted.len() % 2 == 1 {
        sorted[sorted.len() as int / 2]
    } else if sorted.len() == 2 {
        (sorted[0] + sorted[1]) / 2
    } else {
        (sorted[sorted.len() as int / 2 - 1] + sorted[sorted.len() as int / 2]) / 2
    }
}

spec fn sorted_seq(a: Seq<int>) -> Seq<int> {
    a
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use i32 for arithmetic */
fn compute_sum_abs_diffs(a: Vec<i8>, target: i8) -> (sum: i32)
    ensures 
        sum as int == sum_abs_diffs(a@.map(|i: int, x: i8| x as int), target as int)
{
    let mut total: i32 = 0;
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            total as int == sum_abs_diffs(a@.map(|j: int, x: i8| x as int).subrange(0, i as int), target as int),
        decreases a.len() - i
    {
        let diff: i32 = (a[i] as i32) - (target as i32);
        let abs_diff = if diff >= 0 { diff } else { -diff };
        total = total + abs_diff;
        i = i + 1;
    }
    total
}

/* helper modified by LLM (iteration 5): replace unsupported to_vec with manual copy */
fn compute_median(a: &[i8]) -> (median: i8)
    ensures 
        median as int == median_of(a@.map(|i: int, x: i8| x as int))
{
    let mut sorted = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sorted.len() == i,
            forall|j: int| 0 <= j < i ==> sorted@[j] == a@[j],
        decreases a.len() - i
    {
        sorted.push(a[i]);
        i = i + 1;
    }

    let n = sorted.len();
    if n == 0 {
        0
    } else {
        let mut i = 1;
        while i < n
            invariant 
                1 <= i <= n,
                forall|j: int| 0 <= j < i-1 ==> sorted@[j] <= sorted@[j+1],
            decreases n - i
        {
            let mut j = i;
            while j > 0 && sorted[j-1] > sorted[j]
                invariant 
                    0 <= j <= i,
                    forall|k: int| 0 <= k < j-1 ==> sorted@[k] <= sorted@[k+1],
                    forall|k: int| j+1 <= k < i ==> sorted@[k-1] <= sorted@[k],
                    (j > 0 && j < i) ==> sorted@[j-1] <= sorted@[j+1],
                decreases j
            {
                let temp = sorted[j];
                sorted[j] = sorted[j-1];
                sorted[j-1] = temp;
                j = j - 1;
            }
            i = i + 1;
        }

        if n % 2 == 1 {
            sorted[n/2]
        } else if n == 2 {
            (sorted[0] + sorted[1]) / 2
        } else {
            (sorted[n/2 - 1] + sorted[n/2]) / 2
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map(|i: int, x: i8| x as int)),
    ensures 
        result >= 0,
        result as int == sum_abs_diffs(transform(a@.map(|i: int, x: i8| x as int)), median_of(transform(a@.map(|i: int, x: i8| x as int)))),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed, but updating iteration number */
{
    let mut b = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            b.len() == i,
            forall|j: int| 0 <= j < i ==> b@[j] == (a@[j] as int) - (j+1),
        decreases a.len() - i
    {
        let val = a[i] - (i as i8 + 1);
        b.push(val);
        i = i + 1;
    }

    let median = compute_median(&b);
    let sum = compute_sum_abs_diffs(b, median);
    let result = sum as i8;
    result
}
// </vc-code>


}

fn main() {}