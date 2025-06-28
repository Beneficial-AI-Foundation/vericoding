use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|u: int, v: int| from <= u < v < to ==> a[u as usize] <= a[v as usize]
}

fn bubble_sort(a: &mut Vec<i32>)
    requires 
        a.len() > 0,
    ensures 
        sorted(a, 0, a.len()),
        a.len() == old(a).len(),
        // Elements are preserved (multiset equality)
        forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
{
    let n = a.len();
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            a.len() == n,
            // The last i elements are in their final sorted positions
            forall|u: int, v: int| (n - i) <= u < v < n ==> a[u as usize] <= a[v as usize],
            // Elements after position (n-i) are >= all elements before
            forall|u: int, v: int| 0 <= u < (n - i) && (n - i) <= v < n ==> a[u as usize] <= a[v as usize],
            // Multiset is preserved
            forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
    {
        let mut j = 0;
        
        while j < n - 1 - i
            invariant
                i < n,
                j <= n - 1 - i,
                a.len() == n,
                // The largest element in a[0..j+1] is at position j
                forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[j as usize],
                // Previous invariants are maintained
                forall|u: int, v: int| (n - i) <= u < v < n ==> a[u as usize] <= a[v as usize],
                forall|u: int, v: int| 0 <= u < (n - i) && (n - i) <= v < n ==> a[u as usize] <= a[v as usize],
                forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
            }
            j += 1;
        }
        i += 1;
    }
}

// Helper function to count occurrences of an element in a vector
spec fn count_occurrences(a: &Vec<i32>, x: i32) -> nat {
    count_occurrences_range(a, x, 0, a.len())
}

spec fn count_occurrences_range(a: &Vec<i32>, x: i32, from: usize, to: usize) -> nat
    recommends from <= to <= a.len()
    decreases to - from
{
    if from >= to {
        0
    } else if a[from] == x {
        1 + count_occurrences_range(a, x, from + 1, to)
    } else {
        count_occurrences_range(a, x, from + 1, to)
    }
}

} // verus!