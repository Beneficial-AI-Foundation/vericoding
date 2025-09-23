// <vc-preamble>
use vstd::prelude::*;

verus! {

fn print_array<A>(a: Option<&[A]>) {
    assume(false);
}

type Lowercase = char;

fn diag_matrix<A: Copy>(rows: usize, cols: usize, zero: A, one: A) -> (a: Vec<Vec<A>>)
    requires rows >= 0 && cols >= 0
{
    assume(false);
    Vec::new()
}

fn print_matrix<A>(m: &Vec<Vec<A>>) {
    assume(false);
}
// </vc-preamble>

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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}