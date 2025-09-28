// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn popcount_impl(x: u8) -> (count: u8)
    ensures count == popcount(x as nat)
{
    let mut n = x;
    let mut count = 0;
    while n != 0
        invariant
            count + popcount(n as nat) == popcount(x as nat),
        decreases n
    {
        count += n & 1;
        n = n >> 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn sort_array(s: Vec<u8>) -> (sorted: Vec<u8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> popcount(sorted@[i] as nat) <= popcount(sorted@[j] as nat)
            && sorted@.len() == s@.len()
            && s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let mut arr = s;
    let n = arr.len();

    for i in 0..n-1
        invariant
            arr@.to_multiset() == s@.to_multiset(),
            forall|a: int, b: int| 0 <= a < b < i ==> popcount(arr@[a] as nat) <= popcount(arr@[b] as nat),
            forall|a: int, b: int| 0 <= a < i && i <= b < n ==> popcount(arr@[a] as nat) <= popcount(arr@[b] as nat),
    {
        let mut min_index = i;
        for j in i+1..n
            invariant
                i <= min_index < j,
                forall|k: int| i <= k < j ==> popcount(arr@[min_index as int] as nat) <= popcount(arr@[k] as nat),
        {
            if popcount_impl(arr[j]) < popcount_impl(arr[min_index]) {
                min_index = j;
            }
        }
        if min_index != i {
            let temp = arr[i];
            arr[i] = arr[min_index];
            arr[min_index] = temp;
        }
    }
    arr
}
// </vc-code>


}

fn main() {}