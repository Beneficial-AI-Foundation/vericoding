use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|j: int, k: int| start <= j < k < end ==> a[j] <= a[k]
}

// <vc-helpers>
spec fn sorted_prefix(a: &Vec<i32>, i: int) -> bool {
    &&& 0 <= i <= a.len()
    &&& forall|j: int, k: int| 0 <= j < k < i ==> a[j] <= a[k]
}

proof fn sorted_prefix_ensures(a: &Vec<i32>, i: int)
    requires
        0 <= i <= a.len(),
        sorted_prefix(a, i),
        forall|j: int| 0 <= j < i ==> a[j] <= a[i],
    ensures
        sorted_prefix(a, i + 1)
{
    assert(forall|j: int, k: int| 0 <= j < k < i + 1 ==> a[j] <= a[k]) by {
        let j = choose|j: int| #![trigger] 0 <= j && j < k && k < i + 1 && !(a[j] <= a[k]);
        let k = choose|k: int| #![trigger] 0 <= j && j < k && k < i + 1 && !(a[j] <= a[k]);
        if k < i {
            assert(a[j] <= a[k]);
        } else {
            assert(k == i);
            assert(a[j] <= a[k]);
        }
    };
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
fn insertion_sort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 1,
    ensures 
        sorted(a, 0, a.len() as int),
        a.len() == old(a).len()
{
    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sorted_prefix(a, i as int),
            a.len() == old(a).len()
    {
        let mut j: usize = i;
        while j > 0 && a[j - 1] > a[j]
            invariant
                0 <= j <= i <= a.len(),
                sorted_prefix(a, j as int),
                forall|k: int| j <= k < i ==> a[k as usize] <= a[i as usize],
                a.len() == old(a).len()
        {
            a.swap(j - 1, j);
            j = j - 1;
        }
        proof {
            sorted_prefix_ensures(a, j as int);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}