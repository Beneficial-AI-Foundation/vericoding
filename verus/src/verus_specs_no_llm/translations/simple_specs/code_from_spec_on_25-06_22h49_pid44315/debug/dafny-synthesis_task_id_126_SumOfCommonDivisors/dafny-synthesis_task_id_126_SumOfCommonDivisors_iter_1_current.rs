use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumOfCommonDivisors(a: int, b: int) -> (sum: int)
    requires
        a > 0 && b > 0
    ensures
        sum >= 0,
        forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{
    let mut sum = 0;
    let mut i = 1;
    let min_val = if a <= b { a } else { b };
    
    while i <= min_val
        invariant
            1 <= i <= min_val + 1,
            sum >= 0,
            forall d :: 1 <= d < i && d <= a && d <= b && a % d == 0 && b % d == 0 ==> sum >= d,
    {
        if a % i == 0 && b % i == 0 {
            sum = sum + i;
        }
        i = i + 1;
    }
    
    sum
}

}