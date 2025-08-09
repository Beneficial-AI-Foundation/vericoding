use vstd::prelude::*;

verus! {
    // Author of question: Snorri Agnarsson
    // Permalink of question: https://rise4fun.com/Dafny/0HRr

    // Author of solution:    Alexander Guðmundsson
    // Permalink of solution: https://rise4fun.com/Dafny/8pxWd

    // Translated from Dafny to Verus

    /// SearchRecursive translated from Dafny
    /// Searches for element x in sequence a[i..j) using recursion
    /// Returns index of rightmost occurrence of x, or -1 if not found
    spec fn search_recursive(a: Seq<int>, i: int, j: int, x: int) -> int
        decreases j - i
    {
        if !(0 <= i && i <= j && j <= a.len()) {
            -1  // precondition violation
        } else if j == i {
            -1
        } else if a.index(j - 1) == x {
            j - 1
        } else {
            search_recursive(a, i, j - 1, x)
        }
    }

    /// Helper function for search_loop
    /// Implements the while loop logic recursively for spec functions
    spec fn search_loop_helper(a: Seq<int>, i: int, j: int, x: int, t: int) -> int
        decreases t
    {
        if !(0 <= i && i <= j && j <= a.len() && i <= t && t <= j) {
            -1  // precondition violation
        } else if t > i {
            if a.index(t - 1) == x {
                t - 1
            } else {
                search_loop_helper(a, i, j, x, t - 1)
            }
        } else {
            -1
        }
    }

    /// SearchLoop translated from Dafny
    /// Searches for element x in sequence a[i..j) using iteration (modeled recursively)
    /// Returns index of rightmost occurrence of x, or -1 if not found
    spec fn search_loop(a: Seq<int>, i: int, j: int, x: int) -> int
    {
        if !(0 <= i && i <= j && j <= a.len()) {
            -1  // precondition violation
        } else if i == j {
            -1
        } else {
            search_loop_helper(a, i, j, x, j)
        }
    }
}

fn main() {}