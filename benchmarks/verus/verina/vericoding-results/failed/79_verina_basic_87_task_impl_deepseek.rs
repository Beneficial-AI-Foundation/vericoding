// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed executable code syntax and type casting */
fn find_min_exec(s: &Vec<i32>, start: usize) -> (min_index: usize)
    ensures
        start <= min_index < s.len(),
        forall|k: int| start <= k < s.len() as int ==> s[min_index] as int <= s[k as usize] as int
{
    let mut min_index = start;
    let mut i = start + 1;
    while i < s.len()
        invariant
            start <= min_index < s.len(),
            start <= i <= s.len(),
            forall|k: int| start <= k < i as int ==> s[min_index] as int <= s[k as usize] as int,
        decreases s.len() - i
    {
        if s[i] < s[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}

proof fn sorted_lemma(s: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        forall|k: int| i <= k < j ==> s[k] <= s[k+1],
    ensures
        forall|k: int, l: int| i <= k <= l < j ==> s[k] <= s[l]
{
    if i < j {
        let mut k = i;
        while k < j
            invariant
                i <= k <= j,
                forall|m: int, n: int| i <= m <= n < k ==> s[m] <= s[n],
            decreases j - k
        {
            if k > i {
                assert(s[i] <= s[k]);
            }
            k = k + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed executable code syntax and type casting */
    let mut result = a.clone();
    let mut i: usize = 0;
    
    while i < result.len()
        invariant
            i <= result.len(),
            forall|k: int, l: int| 0 <= k <= l < i as int ==> result[k as usize] as int <= result[l as usize] as int,
            result@.subrange(0, i as int).is_sorted(),
            result@ =~= a@,
        decreases result.len() - i
    {
        let min_idx = find_min_exec(&result, i);
        
        let temp = result[i];
        result[i] = result[min_idx];
        result[min_idx] = temp;
        
        proof {
            sorted_lemma(result@, 0, (i + 1) as int);
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}