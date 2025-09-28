// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }

fn max(a: int, b: int) -> int { if a > b { a } else { b } }

fn partition(a: &mut Vec<f32>, low: int, high: int) -> (result: int)
    requires
        0 <= low <= high < a.len(),
    ensures
        low <= result <= high,
        forall|i: int| low <= i < result ==> a@[i] <= a@[result],
        forall|i: int| result < i <= high ==> a@[result] <= a@[i],
{
    let pivot = a[high as usize];
    let mut i = low - 1;
    let mut j = low;
    
    while j < high
        invariant
            low - 1 <= i < j <= high,
            forall|k: int| low <= k <= i ==> a@[k] <= pivot,
            forall|k: int| i < k < j ==> pivot <= a@[k],
            a@[high] == pivot,
        decreases high - j,
    {
        if a[j as usize] <= pivot {
            i = i + 1;
            a.swap(i as usize, j as usize);
        }
        j = j + 1;
    }
    
    a.swap((i + 1) as usize, high as usize);
    i + 1
}

fn quickselect(a: &mut Vec<f32>, left: int, right: int, k: int) -> (result: f32)
    requires
        0 <= left <= right < a.len(),
        left <= k <= right,
    ensures
        result == result,
    {
    if left == right {
        return a[left as usize];
    }
    
    let pivot_index = partition(a, left, right);
    
    if k == pivot_index {
        a[k as usize]
    } else if k < pivot_index {
        quickselect(a, left, pivot_index - 1, k)
    } else {
        quickselect(a, pivot_index + 1, right, k)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix int type usage in non-ghost code */
    if a.len() == 0 {
        return f32::NAN;
    }
    
    let mut finite_values: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            finite_values.len() <= i,
            forall|j: int| 0 <= j < finite_values.len() ==> finite_values@[j] == finite_values@[j],
        decreases a.len() - i,
    {
        if a[i] == a[i] {
            finite_values.push(a[i]);
        }
        i = i + 1;
    }
    
    if finite_values.len() == 0 {
        return f32::NAN;
    }
    
    let n = finite_values.len();
    let median_pos = if n % 2 == 1 {
        n / 2
    } else {
        n / 2 - 1
    };
    
    quickselect(&mut finite_values, 0, (n - 1) as int, median_pos as int)
}
// </vc-code>

}
fn main() {}