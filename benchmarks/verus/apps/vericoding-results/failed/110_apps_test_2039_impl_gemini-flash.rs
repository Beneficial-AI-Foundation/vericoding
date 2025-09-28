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
/* code modified by LLM (iteration 5): fixes compilation error to ensure type `mapped_a` is `Seq<int>` */
{
    if n <= 2 {
        return 0i8;
    }

    let mut count: i8 = 0;
    let mut i: usize = 1; // Change i to usize

    let mapped_a: Seq<int> = a@.map_values(|x: i8| x as int);

    while i < (n as usize) - 1 // Change n to usize
        invariant
            1 <= i,
            i <= (n as usize) - 1,
            count >= 0,
            count <= (i as int),

            count as int == (Set::<int>::new(|k: int| 1 <= k && k < (i as int) && is_local_extremum(mapped_a, k))).len() as int,
        decreases (n as usize) - 1 - i
    {
        // Verus needs help understanding the indexes of an int in the array
        let val_i = a[i];
        let val_i_minus_1 = a[i - 1];
        let val_i_plus_1 = a[i + 1];

        if (val_i > val_i_minus_1 && val_i > val_i_plus_1) || (val_i < val_i_minus_1 && val_i < val_i_plus_1) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}