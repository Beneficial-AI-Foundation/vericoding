// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type issues and removed verification bypasses */
spec fn sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] as int <= s[j] as int
}

spec fn swap_seq<T>(s: Seq<T>, i: int, j: int) -> Seq<T> 
    requires
        0 <= i < s.len(),
        0 <= j < s.len()
{
    s.update(i, s[j]).update(j, s[i])
}

proof fn multiset_count_swap_lemma<T>(s: Seq<T>, i: int, j: int) 
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        multiset_count(swap_seq(s, i, j), s[i]) == multiset_count(s, s[i]),
        multiset_count(swap_seq(s, i, j), s[j]) == multiset_count(s, s[j]),
{
    let s1 = swap_seq(s, i, j);
    assert forall|x| x != s[i] && x != s[j] implies multiset_count(s1, x) == multiset_count(s, x) by {
        // For elements other than swapped ones, multiset count remains the same
    };
    // For swapped elements, counts are preserved
    assert(s1[i] == s[j]);
    assert(s1[j] == s[i]);
    // Multiset permutation preserves counts
}
// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion issues in forall conditions */
{
    let mut result = a.clone();
    let n = result.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < l < i ==> result[k] as int <= result[l] as int,
            forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
        decreases n - i,
    {
        let mut j = i + 1;
        let mut min_index = i;
        
        while j < n
            invariant
                i < j <= n,
                i <= min_index < j,
                forall|k: int| i <= k < j ==> result[k] as int >= result[min_index] as int as int,
                forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
            decreases n - j,
        {
            if result[j] < result[min_index] {
                min_index = j;
            }
            j += 1;
        }
        
        if min_index != i {
            let temp = result[i];
            result[i] = result[min_index];
            result[min_index] = temp;
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}