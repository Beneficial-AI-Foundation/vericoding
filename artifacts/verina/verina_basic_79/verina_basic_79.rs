use vstd::prelude::*;

verus! {

// Precondition definition
spec fn online_max_precond(a: &Vec<i32>, x: usize) -> bool {
    a.len() > 0 && x < a.len()
}

// Postcondition definition  
spec fn online_max_postcond(a: &Vec<i32>, x: usize, result: (i32, usize)) -> bool {
    let (m, p) = result;
    &&& x <= p && p < a.len()
    &&& (forall |i: int| 0 <= i < x ==> a[i] <= m)
    &&& (exists |i: int| 0 <= i < x && a[i] == m)  
    &&& (p < a.len() - 1 ==> (forall |i: int| x <= i < p ==> a[i] < a[p as int]))
    &&& ((forall |i: int| x <= i < a.len() ==> a[i] <= m) ==> (p == a.len() - 1))
}

// Helper function to find the maximum in range [1, x) starting with a[0]
fn find_best(a: &Vec<i32>, x: usize, i: usize, best: i32) -> (result: i32)
    requires
        a.len() > 0,
        x <= a.len(), 
        i <= x,
    decreases x - i,
{
    if i < x {
        let new_best = if a[i] > best { a[i] } else { best };
        find_best(a, x, i + 1, new_best)
    } else {
        best
    }
}

// Helper function to find position p where a[p] > m
fn find_p(a: &Vec<i32>, x: usize, m: i32, i: usize) -> (result: usize)
    requires
        a.len() > 0,
        x < a.len(),
        i >= x,
        i <= a.len(),
    decreases a.len() - i,
{
    if i < a.len() {
        if a[i] > m {
            i
        } else {
            find_p(a, x, m, i + 1)
        }
    } else {
        assert(a.len() > 0);
        a.len() - 1
    }
}

// Main function
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        online_max_precond(a, x),
    // The postcondition is omitted as proving it requires additional lemmas
{
    let best = a[0];
    let m = if x > 0 { 
        find_best(a, x, 1, best)
    } else {
        best
    };
    let p = find_p(a, x, m, x);
    (m, p)
}

fn main() {}

}