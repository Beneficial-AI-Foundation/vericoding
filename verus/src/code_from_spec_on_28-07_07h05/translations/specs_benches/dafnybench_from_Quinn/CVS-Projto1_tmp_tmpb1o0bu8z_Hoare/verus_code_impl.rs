use vstd::prelude::*;

verus! {
    // Max function - returns the maximum of two natural numbers
    fn Max(x: u32, y: u32) -> (r: u32)
        ensures 
            r >= x && r >= y,
            r == x || r == y,
    {
        if x >= y {
            x
        } else {
            y
        }
    }

    // Test function
    fn Test()
    {
        // Empty body is valid for a function with no specifications
    }

    // m1 function 
    fn m1(x: i32, y: i32) -> (z: i32)
        requires 0 < x < y,
        ensures z >= 0 && z <= y && z != x,
    {
        // Need to return a value that is >= 0, <= y, and != x
        // Since 0 < x < y, we know y > 1
        // We can return 0 (which is != x since x > 0)
        0
    }

    // Fibonacci function (recursive specification)
    spec fn fib(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 1 }
        else if n == 1 { 1 }
        else { fib((n - 1) as nat) + fib((n - 2) as nat) }
    }

    // Simple recursive List definition  
    #[derive(PartialEq, Eq)]
    enum List<T> {
        Nil,
        Cons(T, Box<List<T>>)
    }

    // Recursive add function for lists
    spec fn add_list(l: List<i32>) -> int
        decreases l,
    {
        match l {
            List::Nil => 0,
            List::Cons(head, tail) => head as int + add_list(*tail),
        }
    }

    // Maximum element in array
    fn MaxA(a: &[i32]) -> (m: i32)
        requires a.len() > 0,
        ensures 
            forall|i: int| 0 <= i < a.len() ==> a[i] <= m,
            exists|i: int| 0 <= i < a.len() && a[i] == m,
    {
        let mut max = a[0];
        let mut index = 1;
        
        /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
        while index < a.len()
            invariant 
                0 <= index <= a.len(),
                forall|i: int| 0 <= i < index ==> a[i] <= max,
                exists|i: int| 0 <= i < index && a[i] == max,
            decreases a.len() - index,
        {
            if a[index] > max {
                max = a[index];
            }
            index += 1;
        }
        
        max
    }
}

fn main() {}