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
spec fn count_local_extrema_in_range(a: Seq<int>, start: int, end: int) -> int
    /* helper modified by LLM (iteration 5): changed recommends to requires */
    requires 0 <= start <= end <= a.len()
{
    Set::<int>::new(|i: int| start <= i < end && is_local_extremum(a, i)).len() as int
}
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
    /* code modified by LLM (iteration 5): added proof for indexing bounds and fixed loop invariant */
    let mut count = 0;
    if n <= 2 {
        return 0;
    }
    let mut i = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            count as int == count_local_extrema_in_range(a@.map_values(|x: i8| x as int), 1, i as int),
            0 <= 1 <= i <= n as int,
        decreases (n - 1 - i)
    {
        let i_usize = i as usize;
        proof {
            assert(a@.len() == n as int);
            assert(i_usize < (n - 1) as usize);
            assert((n - 1) as usize < n as usize);
        }
        let prev = a[i_usize - 1];
        let curr = a[i_usize];
        let next = a[i_usize + 1];
        if (curr > prev && curr > next) || (curr < prev && curr < next) {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}