use vstd::prelude::*;

verus! {

// Helper function to get element from 2D array  
spec fn get2d(a: Seq<Seq<i32>>, i: int, j: int) -> i32
    recommends 0 <= i < a.len() && 0 <= j < a[i].len()
{
    a[i][j]
}

// Precondition for SlopeSearch
spec fn slope_search_precond(a: Seq<Seq<i32>>, key: i32) -> bool {
    // All rows have the same size
    (forall|i: int, j: int| #![trigger a[i].len(), a[j].len()] 
        0 <= i < a.len() && 0 <= j < a.len() ==> a[i].len() == a[j].len()) &&
    // Each row is sorted
    (forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 
        forall|j: int, k: int| #![trigger a[i][j], a[i][k]] 
            0 <= j <= k < a[i].len() ==> a[i][j] <= a[i][k]) &&
    // Each column is sorted  
    (a.len() == 0 || (a.len() > 0 && a[0].len() == 0) || 
        forall|col: int| #![trigger a[0][col]] 0 <= col < a[0].len() ==>
            forall|row1: int, row2: int| #![trigger a[row1][col], a[row2][col]] 
                0 <= row1 <= row2 < a.len() ==> a[row1][col] <= a[row2][col])
}

// Postcondition for SlopeSearch
spec fn slope_search_postcond(a: Seq<Seq<i32>>, key: i32, result: (i32, i32)) -> bool {
    let (m, n) = result;
    // Either found the key at valid position or key doesn't exist
    ((0 <= m < a.len() && a.len() > 0 && 0 <= n < a[0].len() && 
      get2d(a, m as int, n as int) == key) ||
    (m == -1 && n == -1))
}

#[verifier::external_body]
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (res: (i32, i32))
    requires slope_search_precond(a@.map(|_i, row: Vec<i32>| row@), key)
    ensures slope_search_postcond(a@.map(|_i, row: Vec<i32>| row@), key, res)
{
    if a.len() == 0 {
        return (-1, -1);
    }
    
    if a[0].len() == 0 {
        return (-1, -1);
    }

    // Start from top-right corner: (0, cols-1)
    let mut m = 0i32;
    let mut n = (a[0].len() - 1) as i32;
    
    loop {
        if m >= a.len() as i32 || n < 0 {
            return (-1, -1);
        }
        
        let current = a[m as usize][n as usize];
        
        if current == key {
            return (m, n);
        } else if current < key {
            m = m + 1;
        } else {
            n = n - 1;
        }
    }
}

} // verus!

fn main() {}