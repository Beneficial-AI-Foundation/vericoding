use vstd::prelude::*;

verus! {

// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/0HRr

// Author of solution:    Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/8pxWd

// Use the command
//   verus LinearSearch-skeleton.rs
// to verify the file.

// When you have solved the problem put
// the solution on the Verus web page,
// generate a permalink and put it in
// this file.

// <vc-helpers>
proof fn lemma_seq_index<T>(s: &Vec<T>, i: usize)
    requires
        i < s.len(),
    ensures
        0 <= i as int < s.len() as int,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn search_loop(a: &Vec<i32>, i: usize, j: usize, x: i32) -> (k: i32)
    requires 
        i <= j <= a.len(),
    ensures 
        (i <= k < j) || k == -1,
        k != -1 ==> 0 <= k < a.len() && a[k as int] == x,
        k != -1 ==> forall|r: int| k < r < j && 0 <= r < a.len() ==> a[r] != x,
        k == -1 ==> forall|r: int| (i as int) <= r < (j as int) && 0 <= r < a.len() ==> a[r] != x,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn search_loop(a: &Vec<i32>, i: usize, j: usize, x: i32) -> (k: i32)
    requires 
        i <= j <= a.len(),
    ensures 
        (i <= k < j) || k == -1,
        k != -1 ==> 0 <= k < a.len() && a[k as int] == x,
        k != -1 ==> forall|r: int| k < r < j && 0 <= r < a.len() ==> a[r] != x,
        k == -1 ==> forall|r: int| (i as int) <= r < (j as int) && 0 <= r < a.len() ==> a[r] != x,
{
    let mut k: i32 = -1;
    let mut idx = i;
    while idx < j
        invariant
            i <= idx <= j,
            k == -1 || (i as int <= k < idx as int && 0 <= k < a.len() as int && a[k as int] == x),
            k != -1 ==> forall|r: int| k < r < idx as int && 0 <= r < a.len() as int ==> a[r] != x,
            k == -1 ==> forall|r: int| i as int <= r < idx as int && 0 <= r < a.len() as int ==> a[r] != x,
    {
        if a[idx] == x {
            k = idx as i32;
            break;
        }
        idx = idx + 1;
    }
    k
}
// </vc-code>

fn main() {
}

}