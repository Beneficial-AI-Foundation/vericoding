use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|j: int, k: int| start <= j < k < end ==> a[j] <= a[k]
}

// <vc-helpers>
spec fn multiset_equiv(a: &Vec<i32>, b: &Vec<i32>) -> bool {
    a@.to_multiset() =~= b@.to_multiset()
}

proof fn sorted_extend_lemma(a: &Vec<i32>, start: int, end: int, new_end: int)
    requires
        0 <= start <= end <= new_end <= a.len(),
        sorted(a, start, end),
        forall|j: int| start <= j < end ==> a[j] <= a[new_end - 1],
    ensures
        sorted(a, start, new_end)
{
}

proof fn sorted_subrange_lemma(a: &Vec<i32>, start: int, end: int, sub_start: int, sub_end: int)
    requires
        0 <= start <= sub_start <= sub_end <= end <= a.len(),
        sorted(a, start, end),
    ensures
        sorted(a, sub_start, sub_end)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 1,
    ensures 
        sorted(a, 0, a.len() as int),
        a.len() == old(a).len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let old_a = Ghost(*a);
    
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            sorted(a, 0, i as int),
            a.len() == old_a@.len(),
            multiset_equiv(a, &old_a@),
        decreases a.len() - i
    {
        let key = a[i];
        let mut j = i;
        
        while j > 0 && a[j - 1] > key
            invariant
                0 <= j <= i < a.len(),
                sorted(a, 0, j as int),
                sorted(a, (j + 1) as int, (i + 1) as int),
                forall|k: int| 0 <= k < j ==> a@[k] <= key,
                forall|k: int| j < k <= i ==> a@[k] > key,
                a@[j] == key,
                a.len() == old_a@.len(),
                multiset_equiv(a, &old_a@),
            decreases j
        {
            a.set(j, a[j - 1]);
            j -= 1;
        }
        
        a.set(j, key);
        
        proof {
            sorted_subrange_lemma(a, 0, (i + 1) as int, 0, j as int);
            sorted_subrange_lemma(a, 0, (i + 1) as int, (j + 1) as int, (i + 1) as int);
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}