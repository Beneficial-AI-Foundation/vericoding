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
/* helper modified by LLM (iteration 5): fix syntax error by removing duplicate lemma keyword */
fn lemma_transform_correct(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures transform(a)[i] == a[i] - (i + 1)
{
}

fn lemma_valid_index(n: int, i: int)
    requires 1 <= n <= 127, 0 <= i < n
    ensures 0 <= i < n
{
}

fn lemma_sum_abs_diffs_step(transformed: Seq<int>, median: int, prefix_sum: int, i: nat)
    requires i < transformed.len()
    ensures prefix_sum + abs_int(transformed[i as int] - median) >= 0
{
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
{
    /* code modified by LLM (iteration 5): fix comma placement in assertion */
    let n_usize = n as usize;
    let mut transformed: Vec<i8> = Vec::new();
    
    for i in 0..n
        invariant
            0 <= i <= n,
            transformed.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& j < a@.len()
                &&& j < transformed@.len()
                &&& transformed@[j] == a@[j] - (j + 1)
            },
    {
        proof {
            assert(i < n);
            assert(i as int < a@.len());
        }
        let val = a[i as usize] - (i + 1);
        transformed.push(val);
    }
    
    let mut sorted = transformed.clone();
    
    for i in 0..n
        invariant
            0 <= i <= n,
            sorted.len() == transformed.len(),
            sorted.len() == n,
    {
        for j in (i + 1)..n
            invariant
                i < n,
                i + 1 <= j <= n,
                sorted.len() == n,
                sorted.len() == transformed.len(),
        {
            proof {
                assert(j < n);
                assert(i < n);
                assert(j as usize < sorted.len());
                assert(i as usize < sorted.len());
            }
            if sorted[j as usize] < sorted[i as usize] {
                let temp = sorted[i as usize];
                sorted.set(i as usize, sorted[j as usize]);
                sorted.set(j as usize, temp);
            }
        }
    }
    
    let median = if n % 2 == 1 {
        sorted[(n / 2) as usize]
    } else {
        proof {
            assert(n >= 2);
            assert(n / 2 - 1 >= 0);
            assert((n / 2 - 1) as usize < sorted.len());
            assert((n / 2) as usize < sorted.len());
        }
        (sorted[(n / 2 - 1) as usize] + sorted[(n / 2) as usize]) / 2
    };
    
    let mut sum: i8 = 0;
    
    for i in 0..n
        invariant
            0 <= i <= n,
            sum >= 0,
    {
        proof {
            assert(i < n);
            assert(i as usize < transformed.len());
        }
        let diff = transformed[i as usize] - median;
        let abs_diff = if diff >= 0 { diff } else { -diff };
        sum = sum + abs_diff;
    }
    
    sum
}
// </vc-code>


}

fn main() {}