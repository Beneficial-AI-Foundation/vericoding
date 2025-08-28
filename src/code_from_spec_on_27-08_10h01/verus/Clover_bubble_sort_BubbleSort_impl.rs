use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

proof fn swap_preserves_multiset<T>(v: &Vec<T>, i: usize, j: usize)
    requires 
        i < v.len(),
        j < v.len(),
    ensures
        v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]).to_multiset() == v@.to_multiset()
{
    let original = v@;
    let swapped = original.update(i as int, original[j as int]).update(j as int, original[i as int]);
    
    assert(swapped.to_multiset() =~= original.to_multiset());
}

proof fn bubble_pass_maintains_multiset(v_before: Seq<i32>, v_after: Seq<i32>, n: int)
    requires
        n >= 1,
        v_before.len() == v_after.len(),
        forall|k: int| 0 <= k < n - 1 ==> #[trigger] v_before[k] > v_before[k + 1] ==> {
            v_after == v_before.update(k, v_before[k + 1]).update(k + 1, v_before[k])
        },
        forall|k: int| 0 <= k < n - 1 ==> !(#[trigger] v_before[k] > v_before[k + 1]) ==> {
            v_after == v_before
        }
    ensures
        v_before.to_multiset() == v_after.to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let n = a.len();
    
    for i in 0..n
        invariant
            forall|x: int, y: int| i <= x < y < n ==> a@[x] <= a@[y],
            forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a@[x] <= a@[y],
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        for j in 0..(n - 1 - i)
            invariant
                forall|x: int, y: int| i <= x < y < n ==> a@[x] <= a@[y],
                forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a@[x] <= a@[y],
                forall|x: int| j < x < n - i ==> a@[j as int] <= a@[x],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] > a[j + 1] {
                proof {
                    swap_preserves_multiset(a, j as usize, (j + 1) as usize);
                }
                let temp = a[j];
                let next_val = a[j + 1];
                a.set(j, next_val);
                a.set(j + 1, temp);
            }
        }
    }
}
// </vc-code>

fn main() {
}

}