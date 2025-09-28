// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n
}

spec fn count_local_extrema(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    Set::<int>::new(|i: int| 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))).len() as int
}

spec fn is_local_extremum(a: Seq<int>, i: int) -> bool
    recommends 0 <= i < a.len()
{
    1 <= i < a.len() - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        result >= 0,
        n <= 2 ==> result == 0,
        n > 2 ==> result <= n - 2,
        result as int == count_local_extrema(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Fixed compilation error by removing 'as int' casts from executable i8 comparisons, as 'int' is for ghost code only */
    if n <= 2 {
        return 0;
    }
    assert(valid_input(n as int, a@.map_values(|x: i8| x as int)));
    let mut count: i8 = 0;
    let mut i: usize = 1;
    let n_usize = n as usize;
    while i < n_usize - 1
        invariant
            1 <= i <= n_usize - 1,
            0 <= count as int <= (i - 1) as int,
            count as int == Set::<int>::new(|j: int| 1 <= j < i && 1 <= j < a@.map_values(|x: i8| x as int).len() - 1 && ((a@.map_values(|x: i8| x as int)[j] > a@.map_values(|x: i8| x as int)[j-1] && a@.map_values(|x: i8| x as int)[j] > a@.map_values(|x: i8| x as int)[j+1]) || (a@.map_values(|x: i8| x as int)[j] < a@.map_values(|x: i8| x as int)[j-1] && a@.map_values(|x: i8| x as int)[j] < a@.map_values(|x: i8| x as int)[j+1]))).len() as int,
        decreases n_usize - i
    {
        if ((a[i-1] < a[i] && a[i] > a[i+1]) || (a[i-1] > a[i] && a[i] < a[i+1])) {
            count += 1;
        }
        i += 1;
    }
    return count;
}
// </vc-code>


}

fn main() {}