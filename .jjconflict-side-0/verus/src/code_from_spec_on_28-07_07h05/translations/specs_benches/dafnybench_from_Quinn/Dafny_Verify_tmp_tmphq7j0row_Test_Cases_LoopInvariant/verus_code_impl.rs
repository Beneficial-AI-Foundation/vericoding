use vstd::prelude::*;

verus! {
    fn up_while_less(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == N,
    {
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause to prove termination */
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
        /* code modified by LLM (iteration 1): added decreases clause to prove termination */
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
        /* code modified by LLM (iteration 1): added decreases clause to prove termination */
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
        /* code modified by LLM (iteration 1): added decreases clause to prove termination */
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
        let x = 10;
        let y = 3;
        let q = x / y;
        assert(q == 3);
    }

    fn quotient1()
    {
        let x = 15;
        let y = 4;
        let q = x / y;
        assert(q == 3);
    }
}

fn main() {}