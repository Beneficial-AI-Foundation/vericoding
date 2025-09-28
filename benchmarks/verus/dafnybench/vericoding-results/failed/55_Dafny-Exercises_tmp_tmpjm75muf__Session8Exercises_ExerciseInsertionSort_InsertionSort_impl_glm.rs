use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn lemma_multiset_push<T>(v: Vec<T>, x: T)
    ensures
        v.push(x).to_multiset() =~= v.to_multiset().insert(x),
{
    assert(v.push(x).to_multiset() =~= v.to_multiset().insert(x));
}

proof fn lemma_multiset_swap<T>(v: Vec<T>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
        i != j,
    ensures
        v.swap(i as usize, j as usize).to_multiset() =~= v.to_multiset(),
{
    assert(v.swap(i as usize, j as usize).to_multiset() =~= v.to_multiset());
}

proof fn lemma_sorted_seg_extend(a: Vec<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j + 1 <= a.len(),
        j + 1 <= k < a.len(),
        sorted_seg(a, i, j),
        a[j] <= a[k],
    ensures
        sorted_seg(a, i, k),
{
    assert forall|l: int, m: int| i <= l <= m <= k implies a[l] <= a[m] by {
        if m < k {
            assert(a[l] <= a[m]);
        } else if l <= j {
            assert(a[l] <= a[j] && a[j] <= a[k]);
        } else {
            assert(l == k && m == k);
        }
    }
}

proof fn lemma_sorted_seg_singleton<T>(a: Vec<T>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sorted_seg(a, i, i),
{
    assert forall|l: int, k: int| i <= l <= k <= i implies a[l] <= a[k] by {
        assert(l == i && k == i);
    }
}

proof fn lemma_sorted_seg_after_swap(a: Vec<i32>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
        sorted_seg(a, i, j),
        a[j - 1] > a[j],
        forall|k: int| i <= k < j - 1 ==> a[k] <= a[j],
    ensures
        sorted_seg(a.swap(j-1, j), i, j),
{
    let b = a.swap(j-1, j);
    assert forall|l: int, k: int| i <= l <= k <= j ==> b[l] <= b[k] by {
        if l < j-1 && k < j-1 {
            assert(b[l] == a[l] && b[k] == a[k]);
        } else if l < j-1 && k == j-1 {
            assert(b[l] == a[l] && b[k] == a[j] && a[l] <= a[j]);
        } else if l < j-1 && k == j {
            assert(b[l] == a[l] && b[k] == a[j-1] && a[l] <= a[j] && a[j] < a[j-1]);
        } else if l == j-1 && k == j {
            assert(b[l] == a[j] && b[k] == a[j-1] && a[j] < a[j-1]);
        }
    }
}

proof fn lemma_sorted_seg_prefix(a: Vec<i32>, i: int, j: int)
    requires
        sorted_seg(a, 0, j),
        0 <= i < a.len(),
        i <= j,
    ensures
        sorted_seg(a, 0, i),
{
    assert forall|l: int, k: int| 0 <= l <= k <= i implies a[l] <= a[k] by {
        assert(l <= j && k <= j);
    }
}

proof fn lemma_sorted_seg_mid_insert(a: Vec<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j < a.len(),
        0 <= k < a.len(),
        sorted_seg(a, i, j),
        a[j] <= a[k],
    ensures
        sorted_seg(a, i, j + 1),
{
    assert forall|l: int, m: int| i <= l <= m <= j + 1 implies a[l] <= a[m] by {
        if m < j + 1 {
            assert(a[l] <= a[m]);
        } else if l <= j {
            assert(a[l] <= a[j] && a[j] <= a[k]);
        } else {
            assert(l == j + 1 && m == j + 1);
        }
    }
}

proof fn lemma_sorted_seg_connect(a: Vec<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k < a.len(),
        sorted_seg(a, i, j),
        sorted_seg(a, j, k),
        a[j] <= a[j+1],
    ensures
        sorted_seg(a, i, k),
{
    assert forall|l: int, m: int| i <= l <= m <= k implies a[l] <= a[m] by {
        if m <= j {
            assert(a[l] <= a[m]);
        } else if l >= j {
            assert(a[l] <= a[m]);
        } else {
            assert(a[l] <= a[j] && a[j] <= a[j+1] && a[j+1] <= a[m]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return;
    }

    for i in 1..n
        invariant
            1 <= i <= n,
            sorted_seg(*a, 0, i - 1),
            a@.to_multiset() =~= old(a)@.to_multiset(),
    {
        let mut j = i;
        while j > 0 && a[j - 1] > a[j]
            invariant
                0 < j <= i,
                sorted_seg(*a, 0, j - 2),
                sorted_seg(*a, j, i),
                forall|k: int| 0 <= k < j - 1 ==> a@[k] <= a@[j],
                a@[j - 1] > a@[j],
                a@.to_multiset() =~= old(a)@.to_multiset(),
        {
            a.swap(j - 1, j);
            lemma_multiset_swap(*a, j - 1, j);
            lemma_sorted_seg_after_swap(*a, 0, j);
            j = j - 1;
        }
        if j == 0 {
            lemma_sorted_seg_singleton(*a, 0);
            lemma_sorted_seg_extend(*a, 0, 0, i);
        } else if j == i {
            lemma_sorted_seg_singleton(*a, j);
        } else {
            lemma_sorted_seg_mid_insert(*a, 0, j - 2, j);
            if j > 1 {
                lemma_sorted_seg_connect(*a, 0, j-2, i);
            }
        }
    }
}
// </vc-code>

fn main() {}

}