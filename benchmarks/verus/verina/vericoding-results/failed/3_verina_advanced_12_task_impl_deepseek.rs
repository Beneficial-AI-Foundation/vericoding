// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn has_duplicate_in_range(lst: Seq<i32>, start: int, end: int, val: i32) -> (found: bool) 
    requires 0 <= start <= end <= lst.len()
    ensures found == exists|i: int| start <= i < end && lst[i] == val
{
    if start == end {
        false
    } else {
        has_duplicate_in_range(lst, start, end - 1, val) || lst[end - 1] == val
    }
}

proof fn find_first_duplicate_index(lst: Seq<i32>, i: int, j: int) -> (k: int, l: int)
    requires 
        0 <= i < j < lst.len(),
        lst[i] == lst[j],
        forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
    ensures 
        0 <= k < l < lst.len(),
        lst[k] == lst[l],
        l == i
{
    (i, j)
}
// </vc-helpers>

// <vc-spec>
fn first_duplicate(lst: &Seq<i32>) -> (result: i32)
    ensures

        (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&

        (result != -1 ==> 
            exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == lst[j] && lst[i] == result &&
            forall|k: int, l: int| 0 <= k < l < lst.len() && lst[k] == lst[l] && l <= i ==> k >= i
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error */
    let mut i: usize = 0;
    let n = lst.len() as usize;
    let mut result = -1;
    
    while i < n
        invariant
            i <= n,
            result == -1 ==> forall|k: int, l: int| 0 <= k < l < i as int ==> lst[k] != lst[l],
            result != -1 ==> (
                exists|k: int, l: int| 0 <= k < l < i as int && lst[k] == lst[l] && lst[k] == result &&
                forall|m: int, p: int| 0 <= m < p < i as int && lst[m] == lst[p] && p <= k ==> m >= k
            )
        decreases n - i
    {
        let mut j: usize = i + 1;
        
        while j < n
            invariant
                j <= n,
                result == -1 ==> forall|k: int| i as int <= k < j as int ==> lst[k] != lst[i as int]
            decreases n - j
        {
            if lst[i as int] == lst[j as int] {
                result = lst[i as int];
                break;
            }
            j += 1;
        }
        
        if result != -1 {
            break;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}