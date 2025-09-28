// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> a[i] != a[j])
}

spec fn valid_output(n: int, result: int) -> bool {
    0 <= result <= n
}

spec fn reversed_array(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
{
    Seq::new(a.len(), |i: int| a[a.len() - 1 - i])
}

spec fn has_increasing_pair(ar: Seq<int>) -> bool {
    exists|i: int| 1 <= i < ar.len() && #[trigger] ar[i] > ar[i-1]
}

spec fn min_index(ar: Seq<int>, n: int) -> int {
    0
}

spec fn correct_result(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    let ar = reversed_array(a);
    if has_increasing_pair(ar) {
        let min_i = min_index(ar, n);
        n - min_i
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        valid_output(n as int, result as int) &&
        result as int == correct_result(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant maintenance by correctly tracking the minimum index of increasing pairs */
    let mut i: usize = 1;
    let mut result: i8 = 0;
    
    while i < n as usize
        invariant
            1 <= i <= n as usize,
            n >= 1,
            a.len() == n as usize,
            valid_input(n as int, a@.map_values(|x: i8| x as int)),
            0 <= result as int <= n,
            result as int == 0 ==> forall|j: int| 1 <= j < i as int ==> a[n as usize - 1 - j as usize] as int <= a[n as usize - j as usize] as int,
            result as int > 0 ==> exists|j: int| 1 <= j < i as int && a[n as usize - 1 - j as usize] as int > a[n as usize - j as usize] as int && result as int == n - j,
            result as int > 0 ==> forall|k: int| 1 <= k < i as int && a[n as usize - 1 - k as usize] as int > a[n as usize - k as usize] as int ==> result as int >= n - k
        decreases n as usize - i
    {
        let idx1 = (n as usize - 1 - i) as usize;
        let idx2 = (n as usize - i) as usize;
        
        if a[idx1] > a[idx2] {
            let new_result = (n as i8) - (i as i8);
            if result == 0 || new_result > result {
                result = new_result;
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}