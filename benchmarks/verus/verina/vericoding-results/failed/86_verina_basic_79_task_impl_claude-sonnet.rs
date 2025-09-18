// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed initialization and bounds checking */
    let mut current_max = a[0];
    let mut max_index = 0;
    let mut i = 0;
    
    while i < x
        invariant
            0 <= i <= x,
            0 <= max_index < a.len(),
            max_index < i || i == 0,
            a@[max_index as int] == current_max,
            forall|j: int| 0 <= j < i ==> a@[j] <= current_max,
            i > 0 ==> exists|j: int| 0 <= j < i && a@[j] == current_max,
        decreases x - i
    {
        if a[i] > current_max {
            current_max = a[i];
            max_index = i;
        }
        i += 1;
    }
    
    let mut p = x;
    while p < a.len() - 1
        invariant
            x <= p < a.len(),
            0 <= max_index < a.len(),
            a@[max_index as int] == current_max,
            forall|j: int| 0 <= j < x ==> a@[j] <= current_max,
            exists|j: int| 0 <= j < x && a@[j] == current_max,
            forall|j: int| x <= j < p ==> a@[j] <= current_max,
        decreases a.len() - 1 - p
    {
        if a[p] > current_max {
            return (current_max, p);
        }
        p += 1;
    }
    
    (current_max, a.len() - 1)
}
// </vc-code>

}
fn main() {}