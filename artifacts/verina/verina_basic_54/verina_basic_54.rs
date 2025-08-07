use vstd::prelude::*;

verus! {

// Precondition for CanyonSearch
spec fn canyon_search_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() > 0 && b.len() > 0 && 
    is_sorted(a) && is_sorted(b)
}

// Helper function to check if a sequence is sorted
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Spec version of nat_abs_diff
spec fn spec_nat_abs_diff(x: i32, y: i32) -> nat {
    let diff = (x as int) - (y as int);
    if diff >= 0 { diff as nat } else { (-diff) as nat }
}

// Helper function for absolute difference
fn nat_abs_diff(x: i32, y: i32) -> (result: usize)
    ensures result as nat == spec_nat_abs_diff(x, y)
{
    let diff_i64 = (x as i64) - (y as i64);
    let abs_diff = if diff_i64 >= 0 { diff_i64 } else { -diff_i64 };
    abs_diff as usize
}

// Auxiliary function for canyon search
fn canyon_search_aux(a: &Vec<i32>, b: &Vec<i32>, m: usize, n: usize, d: usize) -> (result: usize)
    requires
        a.len() > 0,
        b.len() > 0,
        m <= a.len(),
        n <= b.len(),
    ensures
        result <= d,
    decreases a.len() + b.len() - m - n
{
    if m < a.len() && n < b.len() {
        let diff = nat_abs_diff(a[m], b[n]);
        let new_d = if diff < d { diff } else { d };
        
        if a[m] <= b[n] {
            canyon_search_aux(a, b, m + 1, n, new_d)
        } else {
            canyon_search_aux(a, b, m, n + 1, new_d)
        }
    } else {
        d
    }
}

// Main CanyonSearch function
fn canyon_search(a: &Vec<i32>, b: &Vec<i32>) -> (result: usize)
    requires
        canyon_search_precond(a@, b@),
{
    let init = nat_abs_diff(a[0], b[0]);
    canyon_search_aux(a, b, 0, 0, init)
}

// Postcondition for CanyonSearch
spec fn canyon_search_postcond(a: Seq<i32>, b: Seq<i32>, result: usize) -> bool {
    // There exists a pair (ai, bi) such that result equals |ai - bi|
    (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && 
        result as nat == spec_nat_abs_diff(a[i], b[j])) &&
    // For all pairs (ai, bi), result <= |ai - bi|
    (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
        result as nat <= spec_nat_abs_diff(a[i], b[j]))
}

}

fn main() {}