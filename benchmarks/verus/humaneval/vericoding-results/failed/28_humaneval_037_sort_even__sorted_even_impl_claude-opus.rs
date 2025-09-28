// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_even_sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j && 2 * i < s.len() && 2 * j < s.len() ==> s[2 * i] <= s[2 * j]
}

/* helper modified by LLM (iteration 2): Fixed return type syntax */
fn partition_even_odd(a: &Vec<i8>) -> (Vec<i8>, Vec<i8>)
    ensures
        result.0@.len() + result.1@.len() == a@.len(),
        forall|i: int| 0 <= i < result.0@.len() ==> exists|j: int| 0 <= j < a@.len() && j % 2 == 0 && result.0@[i] == a@[j],
        forall|i: int| 0 <= i < result.1@.len() ==> exists|j: int| 0 <= j < a@.len() && j % 2 == 1 && result.1@[i] == a@[j],
        result.0@.to_multiset() + result.1@.to_multiset() == a@.to_multiset()
{
    let mut evens = Vec::new();
    let mut odds = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            evens@.to_multiset() + odds@.to_multiset() == a@.subrange(0, i as int).to_multiset(),
            forall|k: int| 0 <= k < evens@.len() ==> exists|j: int| 0 <= j < i && j % 2 == 0 && evens@[k] == a@[j],
            forall|k: int| 0 <= k < odds@.len() ==> exists|j: int| 0 <= j < i && j % 2 == 1 && odds@[k] == a@[j]
    {
        if i % 2 == 0 {
            evens.push(a[i]);
        } else {
            odds.push(a[i]);
        }
        i += 1;
    }
    
    (evens, odds)
}

fn merge_sorted_even_odd(evens: Vec<i8>, odds: Vec<i8>, orig_len: usize) -> Vec<i8>
    requires
        is_even_sorted(evens@),
        orig_len > 0,
        evens@.len() + odds@.len() == orig_len
    ensures
        result@.len() == orig_len,
        is_even_sorted(result@),
        forall|i: int| 0 <= i < result@.len() && i % 2 == 1 ==> 
            exists|j: int| 0 <= j < odds@.len() && result@[i] == odds@[j],
        result@.to_multiset() == evens@.to_multiset() + odds@.to_multiset()
{
    let mut result = Vec::with_capacity(orig_len);
    let mut even_idx = 0;
    let mut odd_idx = 0;
    let mut i = 0;
    
    while i < orig_len
        invariant
            0 <= i <= orig_len,
            0 <= even_idx <= evens.len(),
            0 <= odd_idx <= odds.len(),
            result@.len() == i,
            even_idx + odd_idx == i,
            even_idx == (i + 1) / 2,
            odd_idx == i / 2,
            forall|k: int| 0 <= k < i && k % 2 == 0 ==> result@[k] == evens@[k / 2],
            forall|k: int| 0 <= k < i && k % 2 == 1 ==> result@[k] == odds@[k / 2],
            is_even_sorted(result@)
    {
        if i % 2 == 0 {
            if even_idx < evens.len() {
                result.push(evens[even_idx]);
                even_idx += 1;
            }
        } else {
            if odd_idx < odds.len() {
                result.push(odds[odd_idx]);
                odd_idx += 1;
            }
        }
        i += 1;
    }
    
    result
}

fn sort_evens(evens: Vec<i8>) -> Vec<i8>
    ensures
        result@.len() == evens@.len(),
        is_even_sorted(result@),
        result@.to_multiset() == evens@.to_multiset()
{
    let mut sorted = evens;
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted@.len() == n,
            sorted@.to_multiset() == evens@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i ==> sorted@[k] <= sorted@[l]
    {
        let mut j = i + 1;
        let mut min_idx = i;
        
        while j < n
            invariant
                i < j <= n,
                i <= min_idx < j,
                forall|k: int| i <= k < j ==> sorted@[min_idx] <= sorted@[k]
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i += 1;
    }
    
    sorted
}
// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Updated to match fixed helper signatures */
    let (evens, odds) = partition_even_odd(&a);
    let sorted_evens = sort_evens(evens);
    let result = merge_sorted_even_odd(sorted_evens, odds, a.len());
    result
}
// </vc-code>


}

fn main() {}