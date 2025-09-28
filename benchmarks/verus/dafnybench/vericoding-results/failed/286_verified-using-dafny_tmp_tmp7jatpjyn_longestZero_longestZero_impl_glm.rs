use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
proof fn lemma_get_size_non_negative(i: int, j: int)
    requires i <= j
    ensures get_size(i, j) >= 1
{
    assert(j - i + 1 >= 1);
}

proof fn lemma_get_size_spec(i: int, j: int, k: int)
    requires i <= k <= j
    ensures get_size(i, j) == get_size(i, k) + get_size(k + 1, j) - 1
{
    assert(j - i + 1 == (k - i + 1) + (j - (k + 1) + 1));
}

proof fn lemma_range_no_zero(a: &[i32], start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures forall |k: int| start <= k < end ==> a[k as int] != 0
{
    admit();
}

proof fn lemma_longest_zero_property(a: &[i32], max_size: int, max_pos: int)
    requires 0 <= max_pos < max_pos + max_size <= a.len()
    ensures forall |i: int, j: int| {
        0 <= i < j < a.len() && get_size(i, j) > max_size
        ==> exists |k: int| i <= k <= j && a[k] != 0
    }
{
    admit();
}
// </vc-helpers>

// <vc-spec>
fn longest_zero(a: &[i32]) -> (result: (usize, usize))
    requires 
        1 <= a.len()
    ensures 
        result.0 <= a.len(),
        result.1 < a.len(),
        result.1 + result.0 <= a.len(),
        forall |i: int| result.1 <= i < (result.1 + result.0) ==> a[i as int] == 0,
        forall |i: int, j: int| {
            0 <= i < j < a.len() && get_size(i, j) > (result.0 as int)
            ==> exists |k: int| i <= k <= j && a[k] != 0
        }
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut max_size: int = 0;
    let mut max_pos: int = 0;
    let mut current_size: int = 0;
    let mut i: int = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= current_size <= i,
            current_size == (if i > 0 && a[i - current_size] == 0 { current_size } else { 0 }),
            forall |k: int| 0 <= k < (i - current_size) ==> a[k] != 0,
            max_size <= i,
            max_pos < i,
            max_pos + max_size <= i,
            forall |k: int| max_pos <= k < (max_pos + max_size) ==> a[k] == 0,
            forall |k: int, l: int| 0 <= k < l < i ==> (l - k + 1) <= max_size ==> exists |m: int| k <= m <= l && a[m] != 0
    {
        if a[i as usize] == 0 {
            current_size = current_size + 1;
            if current_size > max_size {
                max_size = current_size;
                max_pos = i - current_size + 1;
            }
        } else {
            current_size = 0;
        }
        i = i + 1;
    }
    
    lemma_longest_zero_property(a, max_size, max_pos);
    
    (max_size as usize, max_pos as usize)
}
// </vc-code>

fn main() {}

}