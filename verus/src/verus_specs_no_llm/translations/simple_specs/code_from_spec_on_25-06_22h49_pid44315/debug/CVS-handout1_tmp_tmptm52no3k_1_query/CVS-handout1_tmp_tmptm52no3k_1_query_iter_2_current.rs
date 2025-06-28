use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i] + sum(a, i + 1, j)
    }
}

fn main() {
}

fn query(a: Vec<int>, i: int, j: int) -> (res: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        res == sum(a@, i, j)
{
    let mut sum_val = 0;
    let mut k = i;
    
    while k < j
        invariant
            i <= k <= j,
            sum_val == sum(a@, i, k),
            0 <= k <= a.len()
        decreases j - k
    {
        assert(0 <= k < a.len());
        assert(k < j);
        sum_val = sum_val + a[k as usize];
        k = k + 1;
    }
    
    sum_val
}

}