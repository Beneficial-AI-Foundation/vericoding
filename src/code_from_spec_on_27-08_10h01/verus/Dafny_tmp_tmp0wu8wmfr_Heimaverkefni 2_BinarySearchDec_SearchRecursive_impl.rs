use vstd::prelude::*;

verus! {

// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   verus H2-skeleton.rs
// to compile the file.

// When you have solved the problem put
// the solution on the Verus web page,
// generate a permalink and put it in
// this file.

// <vc-helpers>
spec fn is_sorted_desc(a: Seq<int>, i: int, j: int) -> bool {
    forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q]
}

proof fn search_recursive_correctness_helper(a: Seq<int>, i: int, j: int, x: int, mid: int)
    requires
        0 <= i < j <= a.len(),
        mid == i + (j - i) / 2,
        i <= mid < j,
        is_sorted_desc(a, i, j)
    ensures
        is_sorted_desc(a, i, mid),
        is_sorted_desc(a, mid + 1, j)
{
    assert forall|p: int, q: int| i <= p < q < mid ==> a[p] >= a[q] by {
        assert(is_sorted_desc(a, i, j));
    }
    assert forall|p: int, q: int| mid + 1 <= p < q < j ==> a[p] >= a[q] by {
        assert(is_sorted_desc(a, i, j));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn search_recursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires 
        0 <= i <= j <= a.len(),
        forall|p: int, q: int| i <= p < q < j ==> a[p] >= a[q],
    ensures 
        i <= k <= j,
        forall|r: int| i <= r < k ==> a[r] >= x,
        forall|r: int| k <= r < j ==> a[r] < x,
    decreases j - i
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if i == j {
        i
    } else {
        let mid = i + (j - i) / 2;
        
        proof {
            search_recursive_correctness_helper(a, i, j, x, mid);
        }
        
        if a[mid] >= x {
            search_recursive(a, mid + 1, j, x)
        } else {
            search_recursive(a, i, mid, x)
        }
    }
}
// </vc-code>

fn main() {
    // Ef eftirfarandi fall er ekki samþykkt þá eru
    // föllin ekki að haga sér rétt að mati Verus.
}

}