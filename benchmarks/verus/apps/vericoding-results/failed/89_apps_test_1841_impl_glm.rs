// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>, queries: Seq<int>) -> bool {
    a.len() == n && queries.len() == m && n >= 1 && m >= 1 &&
    forall|i: int| 0 <= i < m ==> (#[trigger] queries[i], 1 <= queries[i] <= n).1
}

spec fn distinct_count(a: Seq<int>, start: int) -> int
    recommends 0 <= start < a.len()
{
    let suffix_indices = Set::new(|j: int| start <= j < a.len());
    let suffix_values = suffix_indices.map(|j: int| a[j]);
    suffix_values.len() as int
}
// </vc-preamble>

// <vc-helpers>
spec fn set_from_suffix(a: Seq<int>, start: int) -> Set<int>
    recommends 0 <= start <= a.len()
{
    if start >= a.len() {
        Set::empty()
    } else {
        let suffix_indices = Set::new(|j: int| start <= j < a.len());
        suffix_indices.map(|j: int| a[j])
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x| x as int), queries@.map(|i, x| x as int))
    ensures 
        result.len() == m &&
        (forall|i: int| 0 <= i < m ==> (#[trigger] result@[i], result@[i] as int == distinct_count(a@.map(|i, x| x as int), queries@[i] as int - 1)).1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed ghost variable declaration */
{
    let mut distinct_arr: Vec<i8> = vec![0; n as usize];
    let suffix_set: Set<int>;

    distinct_arr[(n-1) as usize] = 1;
    proof {
        let a_seq = a@.map(|i, x| x as int);
        suffix_set = Set::empty().insert(a_seq[(n-1) as int]);
    }

    if n > 1 {
        let mut i = (n-2) as i32;
        while i >= 0
            invariant
                0 <= i+1 < n as int,
                forall|j: int| i+1 <= j < n as int ==> distinct_arr[j] as int == distinct_count(a@.map(|i,x|x as int), j),
                suffix_set == set_from_suffix(a@.map(|i,x|x as int), i+1),
            decreases i
        {
            let idx = i as usize;
            let x = a[idx];
            let x_int = x as int;
            if suffix_set.contains(x_int) {
                distinct_arr[idx] = distinct_arr[idx+1];
            } else {
                distinct_arr[idx] = distinct_arr[idx+1] + 1;
                proof {
                    suffix_set = suffix_set.insert(x_int);
                }
            }
            i = i - 1;
        }
    }

    let mut result: Vec<i8> = Vec::new();
    let mut j = 0;
    while j < m as int
        invariant
            0 <= j <= m as int,
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] as int == distinct_count(a@.map(|i,x|x as int), queries@[k] as int - 1)
        decreases (m as int) - j
    {
        let q = queries[j as usize];
        let q_index = (q - 1) as usize;
        result.push(distinct_arr[q_index]);
        j = j + 1;
    }

    result
}
// </vc-code>


}

fn main() {}