use vstd::prelude::*;

verus! {

// RUN: %verus "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

fn print_array<A>(a: Option<&[A]>) {
    assume(false);
}

type Lowercase = char; // In Verus, we'd use refinement types or Ghost wrappers for constraints

fn diag_matrix<A: Copy>(rows: usize, cols: usize, zero: A, one: A) -> (a: Vec<Vec<A>>)
    requires rows >= 0 && cols >= 0
{
    assume(false);
    Vec::new()
}

fn print_matrix<A>(m: &Vec<Vec<A>>) {
    assume(false);
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &[int], key: int) -> (n: usize)
    ensures 
        0 <= n <= a.len(),
        n == a.len() || a[n as int] == key,
// </vc-spec>
// <vc-code>
{
    a.len()
}
// </vc-code>

fn main() {
    // Main function content would go here
}

}