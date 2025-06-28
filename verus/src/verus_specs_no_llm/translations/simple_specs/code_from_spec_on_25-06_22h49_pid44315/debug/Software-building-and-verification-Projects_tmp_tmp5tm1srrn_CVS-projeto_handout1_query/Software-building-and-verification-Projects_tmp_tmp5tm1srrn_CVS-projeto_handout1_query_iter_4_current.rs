use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
{
    if i >= j {
        0
    } else {
        a[i as usize] + sum(a, i + 1, j)
    }
}

fn main() {
}

fn query(a: Vec<int>, i: int, j: int) -> (res: int)
    requires
        0 <= i <= j <= a.len(),
        i < usize::MAX,
        j < usize::MAX
    ensures
        res == sum(a, i, j)
{
    let mut sum_val = 0;
    let mut k = i;
    
    while k < j
        invariant
            i <= k <= j,
            sum_val == sum(a, i, k),
            0 <= k < usize::MAX
        decreases j - k
    {
        assert(k < j);
        assert(k >= 0);
        assert(k < a.len() as int);
        assert(k < usize::MAX);
        
        sum_val = sum_val + a[k as usize];
        k = k + 1;
    }
    
    sum_val
}

}