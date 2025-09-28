use vstd::prelude::*;

verus! {

// Working through https://dafny.org/dafny/OnlineTutorial/guide

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0nat }
    else if n == 1 { 1nat }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}


spec fn sorted(a: Seq<int>) -> bool {
    forall|n: int, m: int| 0 <= n < m < a.len() ==> a[n] <= a[m]
}



// https://dafny.org/dafny/OnlineTutorial/ValueTypes

spec fn update(s: Seq<int>, i: int, v: int) -> Seq<int>
{
    s.subrange(0, i).add(seq![v]).add(s.subrange(i + 1, s.len() as int))
}


// https://dafny.org/dafny/OnlineTutorial/Lemmas

spec fn count(a: Seq<bool>) -> nat
    decreases a.len()
{
    if a.len() == 0 { 
        0nat
    } else {
        (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
    }
}


struct Node {
    next: Seq<int>, // Using int IDs instead of references for simplicity
}

spec fn closed(graph: Set<int>) -> bool {
    true // Simplified for translation
}

spec fn path(p: Seq<int>, graph: Set<int>) -> bool 
    decreases p.len()
{
    closed(graph) && 0 < p.len() &&
    graph.contains(p[0]) &&
    (p.len() > 1 ==> 
        path(p.subrange(1, p.len() as int), graph))
}

spec fn path_specific(p: Seq<int>, start: int, end: int, graph: Set<int>) -> bool {
    closed(graph) &&
    0 < p.len() && // path is nonempty
    start == p[0] && end == p[p.len() - 1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}

// <vc-helpers>
spec fn get_int_value(a: &[int], i: int) -> int
    requires 0 <= i < a.len()
{
    a[i]
}
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[int]) -> (index: i32)
    requires 
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 0 <= a[i],
        forall|i: int| #![trigger a[i]] 0 < i < a.len() ==> a[i-1] - 1 <= a[i],
    ensures 
        index < 0 ==> forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> a[i] != 0,
        0 <= index ==> index < a.len() && a[index as int] == 0,
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = a.len().checked_sub(1).unwrap_or(0);
    // Use an Option to represent result, None if not found, Some(index) if found
    let mut result: Option<i32> = None;

    if a.len() == 0 {
        return -1;
    }

    // Handle edge case where first element might be 0
    if a[0] == 0 {
        return 0;
    }

    while low <= high
        invariant
            0 <= low,
            low <= a.len(),
            0 <= high,
            high < a.len(), // high can be a.len() - 1, so high < a.len()
            low <= (high as int + 1) as usize, // Loop terminates when low > high
            result.is_none(), // result is only set once 0 is found (to ensure we find earliest 0)
            forall|i: int| #![trigger get_int_value(a, i)] 0 <= i < low as int ==> get_int_value(a, i) != 0,
            forall|i: int| #![trigger get_int_value(a, i)] 0 <= i < a.len() as int ==> 0 <= get_int_value(a, i),
            forall|i: int| #![trigger get_int_value(a, i)] 0 < i < a.len() as int ==> get_int_value(a, i-1) - 1 <= get_int_value(a, i),
    {
        proof {
            if low <= high {
                assert(low < a.len());
                assert(high < a.len());
            }
        }
        let mid_int: int;
        proof {
            mid_int = low as int + (high as int - low as int) / 2;
        }
        let mid: usize = mid_int as usize;

        assert(0 <= mid_int);
        assert(mid_int < a.len());

        assert(0 <= mid);
        assert(mid < a.len()); // mid is within bounds

        if a[mid] == 0 {
            result = Some(mid as i32);
            if mid == 0 {
                break; // Earliest 0 found at index 0
            }
            high = mid - 1; // Search in the left half for an earlier 0
        } else if a[mid] > 0 {
            // Need to handle mid > 0 case before accessing a[mid-1]
            if mid == 0 {
                // If mid is 0 and a[0] > 0, it means the 0 is not at or before mid.
                // We checked a[0] == 0 before the loop. So if we are here, a[0] != 0.
                // Move low to mid + 1 to continue search.
                low = mid + 1;
            } else {
                // Assert that mid - 1 is a valid index
                assert(mid as int - 1 >= 0);
                if a[mid - 1] == 0 {
                    result = Some((mid - 1) as i32);
                    if mid - 1 == 0 {
                        break;
                    }
                    high = mid - 2; // Further reduce search space
                } else {
                    high = mid - 1;
                }
            }
        } else { // a[mid] < 0, this case should not happen given 0 <= a[i]
            // This branch is unreachable due to the precondition `0 <= a[i]`
            // By the precondition: forall|i: int| 0 <= i < a.len() ==> 0 <= a[i]
            // So a[mid] < 0 is impossible.
            // This assert allows Verus to understand this branch is unreachable.
            assert(a[mid] >= 0);
            return -1; // Dead code, but needed for type completeness
        }
    }

    match result {
        Some(idx) => idx,
        None => -1,
    }
}
// </vc-code>

fn main() {
}

}