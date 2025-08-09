use vstd::prelude::*;

verus! {
    fn up_while_less(N: i32) -> (i: i32)
        requires 0 <= N,
        ensures i == N,
    {
        let mut i = 0;
        while i < N
            invariant 0 <= i <= N,
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
        while i != N
            invariant 0 <= i <= N,
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
        while i != 0
            invariant 0 <= i <= N,
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
        while i > 0
            invariant 0 <= i <= N,
        {
            i = i - 1;
        }
        i
    }

    fn quotient()
    {
        let x = 11;
        let y = 3;
        let mut q = 0;
        let mut r = x;
        
        while r >= y
            invariant x == q * y + r && r >= 0,
        {
            q = q + 1;
            r = r - y;
        }
        
        assert(x == q * y + r && 0 <= r < y);
    }

    fn quotient1()
    {
        let x = 15;
        let y = 4;
        let mut q = 0;
        let mut r = x;
        
        while r >= y
            invariant x == q * y + r && r >= 0,
        {
            q = q + 1;
            r = r - y;
        }
        
        assert(x == q * y + r && 0 <= r < y);
    }
}

fn main() {}