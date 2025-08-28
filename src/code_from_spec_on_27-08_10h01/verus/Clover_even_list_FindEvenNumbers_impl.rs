use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn count_even_before(arr: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        count_even_before(arr, i - 1) + if arr[i - 1] % 2 == 0 { 1int } else { 0int }
    }
}

spec fn nth_even_in_array(arr: Seq<i32>, n: int) -> int {
    choose|i: int| 0 <= i < arr.len() && 
        arr[i] % 2 == 0 && 
        count_even_before(arr, i) == n
}

proof fn lemma_count_even_monotonic(arr: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j <= arr.len()
    ensures count_even_before(arr, i) <= count_even_before(arr, j)
    decreases j - i
{
    if i < j {
        lemma_count_even_monotonic(arr, i, j - 1);
    }
}

proof fn lemma_even_ordering_preserved(arr: Seq<i32>, result: Seq<i32>, k: int, l: int)
    requires 
        0 <= k < l < result.len(),
        forall|x: i32| arr.contains(x) && x % 2 == 0 ==> result.contains(x),
        forall|idx: int| 0 <= idx < result.len() ==> result[idx] % 2 == 0,
        forall|idx: int| 0 <= idx < result.len() ==> 
            result[idx] == arr[nth_even_in_array(arr, idx)]
    ensures 
        exists|n: int, m: int| 0 <= n < m < arr.len() && 
        result[k] == arr[n] && result[l] == arr[m]
{
    let n = nth_even_in_array(arr, k);
    let m = nth_even_in_array(arr, l);
    
    lemma_count_even_monotonic(arr, n, m);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut even_numbers = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: i32| arr@.subrange(0, i as int).contains(x) && x % 2 == 0 ==> even_numbers@.contains(x),
            forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x),
            forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0,
            forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
                exists|n: int, m: int| 0 <= n < m < i && 
                even_numbers@[k] == arr@[n] && 
                even_numbers@[l] == arr@[m]
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            even_numbers.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, i as int) =~= arr@);
    }
    
    even_numbers
}
// </vc-code>

fn main() {
}

}