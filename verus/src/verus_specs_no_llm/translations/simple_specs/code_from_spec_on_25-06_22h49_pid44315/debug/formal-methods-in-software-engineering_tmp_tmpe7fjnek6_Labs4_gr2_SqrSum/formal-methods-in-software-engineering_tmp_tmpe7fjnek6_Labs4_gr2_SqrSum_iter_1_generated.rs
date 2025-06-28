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

fn SqrSum(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_spec(n)
    ensures s >= 0
{
    if n <= 0 {
        0
    } else {
        let prev_sum = SqrSum(n - 1);
        prev_sum + n * n
    }
}

}