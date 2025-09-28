use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_to_multiset_swap<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    reveal_with_fuel(Seq::to_multiset_update, 2);
    assert(s.update(i, s[j]).update(j, s[i]).to_multiset() == 
           s.to_multiset().remove(s[i]).insert(s[j]).remove(s[j]).insert(s[i]));
}

proof fn lemma_seq_to_multiset_sub<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        s.subrange(i, j).to_multiset().subset_of(s.to_multiset()),
{
    reveal_with_fuel(Seq::to_multiset_subrange, 2);
}

proof fn lemma_seq_to_multiset_cons<T>(s: Seq<T>, x: T, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.insert(i, x).to_multiset() == s.to_multiset().insert(x),
{
    reveal_with_fuel(Seq::to_multiset_insert, 2);
}

proof fn lemma_seq_to_multiset_update<T>(s: Seq<T>, i: int, x: T)
    requires
        0 <= i < s.len(),
    ensures
        s.update(i, x).to_multiset() == s.to_multiset().remove(s[i]).insert(x),
{
    reveal_with_fuel(Seq::to_multiset_update, 2);
}

proof fn selection_sort_permutation_invariant<T>(old_seq: Seq<T>, current_seq: Seq<T>, n: int, i: int)
    requires
        0 <= i <= n <= current_seq.len(),
        current_seq.subrange(i, n).to_multiset() == old_seq.subrange(i, n).to_multiset(),
    ensures
        current_seq.to_multiset() == old_seq.to_multiset(),
{
    let left = current_seq.subrange(0, i);
    let right = current_seq.subrange(i, n);
    let old_left = old_seq.subrange(0, i);
    let old_right = old_seq.subrange(i, n);
    
    assert(right.to_multiset() == old_right.to_multiset());
    
    assert(current_seq.to_multiset() == left.to_multiset().add(right.to_multiset()));
    assert(old_seq.to_multiset() == old_left.to_multiset().add(old_right.to_multiset()));
}

proof fn lemma_usize_int_conversion(val: usize)
    ensures
        val as int == val,
{
}

proof fn lemma_int_usize_conversion(val: int)
    requires
        0 <= val,
    ensures
        val as usize == val,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let old_a: Seq<i32> = a@;
    let n: usize = a.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < i as int && i as int <= l < n as int ==> a[k as usize] <= a[l as usize],
            forall|k: int| 0 <= k < i as int ==> a[k as usize] <= a[i],
            a@.to_multiset() == old_a.to_multiset(),
        decreases n - i,
    {
        let mut min_index: usize = i;
        let mut j: usize = i + 1;
        
        while j < n
            invariant
                i <= j <= n,
                i <= min_index < n,
                forall|k: int| i as int <= k < j as int ==> a[min_index] <= a[k as usize],
                a@.to_multiset() == old_a.to_multiset(),
            decreases n - j,
        {
            if a[j] < a[min_index] {
                min_index = j;
            }
            j = j + 1;
        }
        
        if i != min_index {
            let tmp = a[i];
            a[i] = a[min_index];
            a[min_index] = tmp;
            proof {
                lemma_seq_to_multiset_swap(a@, i as int, min_index as int);
                lemma_usize_int_conversion(i);
                lemma_usize_int_conversion(min_index);
            }
        }
        
        proof {
            lemma_usize_int_conversion(i);
            lemma_usize_int_conversion(n);
            
            assert(forall|k: int| i as int <= k < n as int ==> a[i] <= a[k as usize]);
            assert(forall|k: int, l: int| 0 <= k < i as int && i as int <= l < n as int ==> a[k as usize] <= a[l as usize]);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}