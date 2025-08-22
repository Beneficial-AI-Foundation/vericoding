use vstd::prelude::*;

verus! {
    spec fn Average(a: int, b: int) -> int {
        (a + b) / 2
    }

    proof fn Triple(x: int) -> (r: int)
        ensures r == 3 * x
    {
        let r = Average(2 * x, 4 * x);
        assert((2 * x + 4 * x) / 2 == 6 * x / 2);
        assert(6 * x / 2 == 3 * x);
        r
    }

    fn Triple1(x: i32) -> (r: i32)
        requires -715827882 <= x <= 715827882  // Prevent overflow
        ensures r == 3 * x
    {
        3 * x
    }

    proof fn DoubleQuadruple(x: int) -> (res: (int, int))
        ensures res.0 == 2 * x && res.1 == 4 * x
    {
        let a = 2 * x;
        let b = 2 * a;
        (a, b)
    }

    fn F() -> (r: i32)
        ensures r == 29
    {
        29
    }

    fn M() -> (r: i32)
        ensures r == 29
    {
        29
    }

    fn Caller() {
    }

    fn MyMethod(x: i32) -> (y: i32)
        requires 10 <= x <= 1000  // Prevent overflow and ensure postcondition
        ensures 25 <= y
    {
        x + 15
    }
}

fn main() {}