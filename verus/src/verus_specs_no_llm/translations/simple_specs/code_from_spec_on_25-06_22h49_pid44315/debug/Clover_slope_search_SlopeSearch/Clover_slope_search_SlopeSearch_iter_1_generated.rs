use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SlopeSearch(a: array2<int>, key: int) -> (m: int, n: int)
    requires
        forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a.spec_index(i,j)<=a.spec_index(i,j'),
        forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a.spec_index(i,j)<=a.spec_index(i',j),
        exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a.spec_index(i,j)==key
    ensures
        0<=m<a.Length0 && 0<=n<a.Length1,
        a.spec_index(m,n)==key
{
    let mut i: int = 0;
    let mut j: int = a.Length1 - 1;
    
    while i < a.Length0 && j >= 0
        invariant
            0 <= i <= a.Length0,
            -1 <= j < a.Length1,
            i < a.Length0 && j >= 0 ==> (
                forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a.spec_index(r, c) < key,
                forall r, c :: 0 <= r < a.Length0 && j < c < a.Length1 ==> a.spec_index(r, c) > key
            ),
            exists r, c :: 0 <= r < a.Length0 && 0 <= c < a.Length1 && a.spec_index(r, c) == key
    {
        if a.spec_index(i, j) == key {
            return (i, j);
        } else if a.spec_index(i, j) < key {
            i = i + 1;
        } else {
            j = j - 1;
        }
    }
    
    // This should never be reached due to the precondition
    // but we need to return something to satisfy the compiler
    let mut found_i: int = 0;
    let mut found_j: int = 0;
    
    let mut row: int = 0;
    while row < a.Length0 {
        let mut col: int = 0;
        while col < a.Length1 {
            if a.spec_index(row, col) == key {
                found_i = row;
                found_j = col;
                return (found_i, found_j);
            }
            col = col + 1;
        }
        row = row + 1;
    }
    
    return (found_i, found_j);
}

}

The implementation uses a "staircase search" algorithm that starts from the top-right corner of the array:

   - If equal: found the key, return the position
   - If less than key: move down (increment row)
   - If greater than key: move left (decrement column)

This algorithm is efficient because it eliminates either a complete row or column in each iteration, taking advantage of the sorted property in both dimensions.

The fallback linear search at the end should never execute due to the precondition guaranteeing the key exists, but it's included to ensure the function always returns valid coordinates that satisfy the postcondition.