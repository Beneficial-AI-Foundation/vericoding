use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
proof fn seq_swap<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
    requires 0 <= i < s.len() && 0 <= j < s.len(),
    ensures s.len() == len(s),
    ensures forall |k: int| 0 <= k < s.len() && k != i && k != j ==> s[k] == s[k],
    ensures s[i] == s[j],
    ensures s[j] == s[i],
{
    assert(forall |k: int| 0 <= k < s.len() && k != i && k != j ==>
        #[trigger] s[k] == s[k]);
    s.update(i, s[j]).update(j, s[i])
}

proof fn lemma_multiset_swap<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i < s.len() && 0 <= j < s.len(),
    ensures s.to_multiset() =~= seq_swap(s, i, j).to_multiset(),
{
    let s_prime = seq_swap(s, i, j);
    assert(s_prime.to_multiset() =~= s.to_multiset());
}

fn find_min_index(a: &Vec<int>, start: int) -> (min_index: int)
    requires 0 <= start < a.len() as int,
    ensures start <= min_index < a.len() as int,
    ensures forall |i: int| start <= i < a.len() as int ==> #[trigger] a@[min_index] <= a@[i],
{
    let mut min_index = start;
    let mut i = start + 1;
    
    while i < a.len() as int
        invariant start <= min_index < a.len() as int,
        invariant start <= i <= a.len() as int,
        invariant forall |k: int| start <= k < i ==> a@[min_index] <= a@[k],
    {
        if a@[i] < a@[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len() as int;
    let mut i = 0;
    
    while i < n
        invariant 0 <= i <= n,
        invariant ordered(a@, 0, i),
        invariant a.len() == n,
        invariant a@.to_multiset() =~= old(a)@.to_multiset(),
    {
        let min_index = find_min_index(a, i);
        
        if min_index != i {
            a.swap(i as usize, min_index as usize);
            lemma_multiset_swap(a@, i, min_index);
        }
        
        proof {
            if i > 0 {
                assert(forall |k: int| i < k < n ==> a@[k-1] <= a@[k]);
            }
        }
        
        i = i + 1;
    }
    
    assert(n <= i <= n);
    assert(ordered(a@, 0, n));
}
// </vc-code>

fn main() {}

}