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
/* helper modified by LLM (iteration 2): added spec function to count extrema in a prefix of the array */
spec fn count_local_extrema_prefix(a: Seq<int>, k: int) -> int
{
    Set::<int>::new(|i: int| 1 <= i < k && is_local_extremum(a, i)).len() as int
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
    /* code modified by LLM (iteration 2): used int for loop counter and added proof blocks for verification */
    let ghost a_int = a@.map_values(|x: i8| x as int);
    if n <= 2 {
        proof {
            let n_int = n as int;
            assert forall |i: int| !(1 <= i < n_int - 1) by {
                requires n_int <= 2;
                assert(n_int - 1 <= 1);
            }
            assert(count_local_extrema(n_int, a_int) == 0);
        }
        return 0;
    }

    let mut count: i8 = 0;
    let mut i: int = 1;
    let n_int = n as int;

    while i < n_int - 1
        invariant
            n > 2,
            valid_input(n_int, a_int),
            1 <= i < n_int,
            count >= 0,
            count as int == count_local_extrema_prefix(a_int, i),
        decreases n_int - 1 - i
    {
        assert(0 <= i < a@.len());
        assert(0 <= i - 1 < a@.len());
        assert(0 <= i + 1 < a@.len());

        let prev = a[(i - 1) as usize];
        let current = a[i as usize];
        let next = a[(i + 1) as usize];

        let is_ext = (current > prev && current > next) || (current < prev && current < next);
        
        proof {
            assert(1 <= i < a_int.len() - 1);
            assert(is_ext == is_local_extremum(a_int, i));
            assert(count_local_extrema_prefix(a_int, i + 1) == count_local_extrema_prefix(a_int, i) + if is_ext { 1 } else { 0 });
        }

        if is_ext {
            count = count + 1;
        }

        i = i + 1;
    }

    proof {
        assert(i == n_int - 1);
        assert(count as int == count_local_extrema_prefix(a_int, n_int - 1));
        assert(count_local_extrema_prefix(a_int, n_int - 1) == count_local_extrema(n_int, a_int));
    }

    count
}
// </vc-code>


}

fn main() {}