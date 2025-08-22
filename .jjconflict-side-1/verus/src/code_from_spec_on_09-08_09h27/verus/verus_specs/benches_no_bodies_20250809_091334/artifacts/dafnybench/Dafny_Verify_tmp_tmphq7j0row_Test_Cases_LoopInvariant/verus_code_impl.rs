use vstd::prelude::*;

verus! {
    fn up_while_less(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == N,
    {
        let mut i = 0;
        /* code modified by LLM (iteration 1): Added decreases clause to prove termination */
        while i < N
            invariant 0 <= i <= N,
            decreases N - i,
        {
            i = i + 1;
        }
        i
    }

    fn up_while_not_equal(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == N,
    {
        let mut i = 0;
        /* code modified by LLM (iteration 1): Added decreases clause to prove termination */
        while i != N
            invariant 0 <= i <= N,
            decreases N - i,
        {
            i = i + 1;
        }
        i
    }

    fn down_while_not_equal(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == 0,
    {
        let mut i = N;
        /* code modified by LLM (iteration 1): Added decreases clause to prove termination */
        while i != 0
            invariant 0 <= i <= N,
            decreases i,
        {
            i = i - 1;
        }
        i
    }

    fn down_while_greater(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == 0,
    {
        let mut i = N;
        /* code modified by LLM (iteration 1): Added decreases clause to prove termination */
        while i > 0
            invariant 0 <= i <= N,
            decreases i,
        {
            i = i - 1;
        }
        i
    }

    fn quotient()
    {
        /* code modified by LLM (iteration 1): Added explicit type annotations and decreases clause */
        let x: i32 = 11;
        let y: i32 = 3;
        let mut q: i32 = 0;
        let mut r: i32 = x;
        
        while r >= y
            invariant x == q * y + r && r >= 0,
            decreases r,
        {
            q = q + 1;
            r = r - y;
        }
        
        assert(x == q * y + r && 0 <= r < y);
    }

    fn quotient1()
    {
        /* code modified by LLM (iteration 1): Added explicit type annotations and decreases clause */
        let x: i32 = 15;
        let y: i32 = 4;
        let mut q: i32 = 0;
        let mut r: i32 = x;
        
        while r >= y
            invariant x == q * y + r && r >= 0,
            decreases r,
        {
            q = q + 1;
            r = r - y;
        }
        
        assert(x == q * y + r && 0 <= r < y);
    }
}

fn main() {}