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
    /* code modified by LLM (iteration 3): fixed casting and bounds issues */
    // Since n >= 1 from precondition, n as usize is safe
    assert(n >= 1);
    assert(a@.len() == n);
    
    let mut transformed: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            n >= 1,
            n_usize == n as usize,
            a@.len() == n,
            i <= n_usize,
            i == transformed.len(),
            transformed@.len() == i as int,
            forall|j: int| 0 <= j < i ==> transformed@[j] == (a@[j] - (j + 1)) as i8,
        decreases n_usize - i
    {
        assert(i < n_usize);
        assert(i < a@.len());
        
        // Use checked arithmetic to avoid overflow
        let i_i8 = i as i8;
        let val: i8 = if a[i] >= i_i8 + 1 {
            a[i] - (i_i8 + 1)
        } else {
            // Handle potential underflow
            let diff = (i_i8 + 1) - a[i];
            0i8 - diff
        };
        
        transformed.push(val);
        i = i + 1;
    }

    // Find median
    let median: i8 = if transformed.len() == 0 {
        0
    } else if transformed.len() % 2 == 1 {
        transformed[transformed.len() / 2]
    } else if transformed.len() == 2 {
        let sum = if transformed[0] >= 0 && transformed[1] >= 0 {
            transformed[0] + transformed[1]
        } else if transformed[0] < 0 && transformed[1] < 0 {
            transformed[0] + transformed[1]
        } else {
            transformed[0] + transformed[1]
        };
        sum / 2
    } else {
        let idx1 = transformed.len() / 2 - 1;
        let idx2 = transformed.len() / 2;
        let sum = if transformed[idx1] >= 0 && transformed[idx2] >= 0 {
            transformed[idx1] + transformed[idx2]
        } else if transformed[idx1] < 0 && transformed[idx2] < 0 {
            transformed[idx1] + transformed[idx2]
        } else {
            transformed[idx1] + transformed[idx2]
        };
        sum / 2
    };

    // Calculate sum of absolute differences
    let mut sum: i8 = 0;
    let mut k: usize = 0;
    
    while k < transformed.len()
        invariant
            k <= transformed.len(),
            sum >= 0,
        decreases transformed.len() - k
    {
        let diff = if transformed[k] >= median {
            transformed[k] - median
        } else {
            median - transformed[k]
        };
        
        // Check for overflow before adding
        if sum <= 127 - diff {
            sum = sum + diff;
        } else {
            // Saturate at max value
            sum = 127;
        }
        
        k = k + 1;
    }

    sum
}
// </vc-code>


}

fn main() {}