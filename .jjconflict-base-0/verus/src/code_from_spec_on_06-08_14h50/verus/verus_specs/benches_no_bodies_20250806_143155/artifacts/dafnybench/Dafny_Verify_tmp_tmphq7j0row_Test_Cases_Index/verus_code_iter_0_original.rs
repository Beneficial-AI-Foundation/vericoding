use vstd::prelude::*;

verus! {
    proof fn index(n: int) -> (i: int)
        requires 1 <= n
        ensures 0 <= i < n
    {
        n / 2
    }

    proof fn min(x: int, y: int) -> (m: int)
        ensures 
            m <= x && m <= y,
            m == x || m == y
    {
        let m = if x >= y {
            y
        } else {
            x
        };
        assert(m <= x && m <= y);
        m
    }

    proof fn max(x: int, y: int) -> (m: int)
        ensures 
            m >= x && m >= y,
            m == x || m == y
    {
        let m = if x >= y {
            x
        } else {
            y
        };
        assert(m >= x && m >= y);
        m
    }

    proof fn max_sum(x: int, y: int) -> (result: (int, int))
        ensures 
            result.0 == x + y,
            result.1 == if x >= y { x } else { y }
    {
        let s = x + y;
        let m = if x >= y {
            x
        } else {
            y
        };
        (s, m)
    }

    proof fn max_sum_caller()
    {
        let x = 1928;
        let y = 1;
        let (a, b) = max_sum(x, y);

        assert(a == 1929);
        assert(b == 1928);
    }

    proof fn reconstruct_from_max_sum(s: int, m: int) -> (result: (int, int))
        requires s <= 2 * m
        ensures 
            s == (result.0 + result.1),
            (m == result.0 || m == result.1) && result.0 <= m && result.1 <= m
    {
        let x = m;
        let y = s - m;
        (x, y)
    }

    proof fn test_max_sum(x: int, y: int)
    {
        let (s, m) = max_sum(x, y);
        let (xx, yy) = reconstruct_from_max_sum(s, m);
        assert((xx == x && yy == y) || (xx == y && yy == x));
    }
}

fn main() {}