use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
use vstd::multiset::Multiset;

spec fn multiset_of_seq(s: Seq<int>) -> Multiset<int> {
    s.to_multiset()
}

proof fn insertion_sort_preserves_multiset(array: Seq<int>, i: int, j: int, val: int)
    requires 
        0 <= i < j < array.len(),
        array[j] == val
    ensures 
        multiset_of_seq(array) == multiset_of_seq(array.update(i, val).update(j, array[i]))
{
    let new_array = array.update(i, val).update(j, array[i]);
    assert(multiset_of_seq(array) == multiset_of_seq(new_array));
}

proof fn sorted_extension_lemma(array: Seq<int>, pos: int, val: int)
    requires 
        0 < pos < array.len(),
        insertion_sorted(array, 0, pos),
        forall|k: int| 0 <= k < pos ==> array[k] <= val
    ensures 
        insertion_sorted(array.update(pos, val), 0, pos + 1)
{
    let new_array = array.update(pos, val);
    assert forall|i: int, j: int| 0 <= i < j < pos + 1 implies new_array[i] <= new_array[j] by {
        if j == pos {
            assert(new_array[j] == val);
            assert(array[i] <= val);
        } else {
            assert(new_array[i] == array[i]);
            assert(new_array[j] == array[j]);
            assert(array[i] <= array[j]);
        }
    }
}

proof fn multiset_update_preserves(s: Seq<int>, i: int, val: int)
    requires 0 <= i < s.len()
    ensures multiset_of_seq(s.update(i, val)) == multiset_of_seq(s).remove(s[i]).insert(val)
{
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i = 1;
    
    while i < array.len()
        invariant 
            i >= 1,
            i <= array.len(),
            insertion_sorted(array@, 0, i as int),
            multiset_of_seq(array@) == multiset_of_seq(old(array)@)
        decreases array.len() - i
    {
        let key = array[i];
        let mut j = i;
        
        while j > 0 && array[j - 1] > key
            invariant 
                0 <= j <= i,
                j < array.len(),
                i < array.len(),
                key == array@[i as int],
                insertion_sorted(array@, 0, j as int),
                insertion_sorted(array@, (j as int) + 1, (i as int) + 1),
                forall|k: int| j as int <= k <= i as int ==> array@[k] == key,
                forall|k: int| 0 <= k < j as int ==> array@[k] <= key,
                multiset_of_seq(array@) == multiset_of_seq(old(array)@)
            decreases j
        {
            let temp = array[j - 1];
            array.set(j, temp);
            j = j - 1;
        }
        
        array.set(j, key);
        
        proof {
            sorted_extension_lemma(array@, i as int, key);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}