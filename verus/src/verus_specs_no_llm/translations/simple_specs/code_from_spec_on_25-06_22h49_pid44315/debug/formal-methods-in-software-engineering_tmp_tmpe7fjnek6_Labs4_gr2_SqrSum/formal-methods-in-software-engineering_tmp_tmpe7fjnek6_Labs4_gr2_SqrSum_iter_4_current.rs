use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sqr_sum_spec(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        n * n + sqr_sum_spec(n - 1)
    }
}

fn SqrSum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == sqr_sum_spec(n as int)
    ensures s >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev_sum = SqrSum(n - 1);
        assert(prev_sum == sqr_sum_spec((n - 1) as int));
        let n_squared = n * n;
        let result = prev_sum + n_squared;
        assert(result == (n as int) * (n as int) + sqr_sum_spec((n - 1) as int));
        assert(result == sqr_sum_spec(n as int));
        result
    }
}

}