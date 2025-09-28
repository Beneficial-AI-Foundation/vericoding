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
/* helper modified by LLM (iteration 5): Fixed syntax for sequence conversion and added proper ghost tracking */
fn is_local_extremum_helper(a: &Vec<i8>, i: usize) -> bool
    requires 
        1 <= i < a.len() - 1
{
    let prev = a[i - 1];
    let curr = a[i];
    let next = a[i + 1];
    (curr > prev && curr > next) || (curr < prev && curr < next)
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
/* code modified by LLM (iteration 5): Fixed sequence conversion syntax and loop verification */
{
    if n <= 2 {
        return 0;
    }
    
    let mut count: i8 = 0;
    let mut i: i8 = 1;
    ghost {
        let a_seq = a@.map_values(|x: i8| x as int);
    }
    
    while i < n - 1
        invariant 
            1 <= i <= n,
            count >= 0,
            count as int == count_local_extrema(i as int, a@.map_values(|x: i8| x as int))
        decreases n - i
    {
        if is_local_extremum_helper(&a, i as usize) {
            count += 1;
        }
        i += 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}