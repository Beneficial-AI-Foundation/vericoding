// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_with_pred(s: Seq<i8>, p: Seq<bool>) -> bool
    recommends s.len() == p.len()
{
    forall|i: int, j: int| 0 <= i < j < s.len() && p[i] && p[j] ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 5): Added decreases clause to inner while loop */
fn bubble_sort_pred(s: &mut Vec<i8>, p: &Vec<bool>)
    requires
        old(s).len() == p.len(),
    ensures
        s.len() == old(s).len(),
        s@.to_multiset() == old(s)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < s.len() && p[i] && p[j] ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() && !p[i] ==> s[i] == old(s)[i],
{
    let n = s.len();
    let mut changed = true;
    let mut pass = 0;
    
    while changed
        invariant
            s.len() == n,
            n == p.len(),
            s@.to_multiset() == old(s)@.to_multiset(),
            forall|i: int| 0 <= i < n && !p[i] ==> s[i] == old(s)[i],
            pass <= n,
            forall|i: int, j: int| 0 <= i < j < n - pass && p[i] && p[j] ==> s[i] <= s[j],
            forall|i: int, j: int| n - pass <= i < j < n && p[i] && p[j] ==> s[i] <= s[j],
            forall|k: int, l: int| 0 <= k < n - pass && n - pass <= l < n && p[k] && p[l] ==> s[k] <= s[l],
        decreases n - pass
    {
        changed = false;
        let mut i = 0;
        
        while i < n - 1 - pass
            invariant
                s.len() == n,
                n == p.len(),
                0 <= i <= n - 1 - pass,
                pass < n,
                s@.to_multiset() == old(s)@.to_multiset(),
                forall|k: int| 0 <= k < n && !p[k] ==> s[k] == old(s)[k],
                forall|j: int| 0 <= j <= i && j < n - 1 && p[j] && p[j + 1] ==> s[j] <= s[j + 1],
                forall|k: int, l: int| 0 <= k < l <= i && p[k] && p[l] ==> s[k] <= s[l],
                forall|k: int, l: int| i < k < l < n - pass && p[k] && p[l] ==> s[k] <= s[l],
                forall|k: int, l: int| n - pass <= k < l < n && p[k] && p[l] ==> s[k] <= s[l],
                forall|k: int, l: int| 0 <= k <= i && n - pass <= l < n && p[k] && p[l] ==> s[k] <= s[l],
                forall|k: int, l: int| 0 <= k <= i && i < l < n - pass && p[k] && p[l] ==> s[k] <= s[l],
            decreases n - 1 - pass - i
        {
            if p[i] && p[i + 1] && s[i] > s[i + 1] {
                proof {
                    let old_slice = s@.skip(i as int).take(2);
                    assert(old_slice.len() == 2);
                    assert(old_slice[0] == s@[i as int]);
                    assert(old_slice[1] == s@[(i + 1) as int]);
                }
                let temp = s[i];
                s.set(i, s[i + 1]);
                s.set(i + 1, temp);
                changed = true;
                proof {
                    let new_slice = s@.skip(i as int).take(2);
                    assert(new_slice.len() == 2);
                    assert(new_slice[0] == s@[i as int]);
                    assert(new_slice[1] == s@[(i + 1) as int]);
                    assert(s@.to_multiset() =~= old(s)@.to_multiset());
                }
            }
            i = i + 1;
        }
        pass = pass + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Main function body unchanged */
    let mut result = s.clone();
    bubble_sort_pred(&mut result, &p);
    result
}
// </vc-code>


}

fn main() {}