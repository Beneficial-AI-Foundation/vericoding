use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_swap_preserves_multiset<T>(v: &Vec<T>, i: usize, j: usize)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        {
            let mut new_v = v.clone();
            new_v.swap(i, j);
            new_v@.to_multiset() == v@.to_multiset()
        }
{
    let mut new_v = v.clone();
    new_v.swap(i, j);
    assert(new_v@.to_multiset() == v@.to_multiset()) by {
        reveal(Seq::to_multiset);
    };
}

proof fn lemma_swap_effects<T>(v: &Vec<T>, i: usize, j: usize, ghost_old_v: Ghost<Seq<T>>)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
        ghost_old_v@ == old(v)@,
    ensures
        {
            let mut new_v = v.clone();
            new_v.swap(i, j);
            forall|k: int| 0 <= k < v.len() ==> #![trigger new_v@[k], ghost_old_v@[k]] (
                (k == i ==> new_v@[k] == ghost_old_v@[j]) &&
                (k == j ==> new_v@[k] == ghost_old_v@[i]) &&
                (k != i && k != j ==> new_v@[k] == ghost_old_v@[k])
            )
        }
{
    let mut new_v = v.clone();
    new_v.swap(i, j);
    assert forall|k: int| 0 <= k < v.len() implies (
        (k == i ==> new_v@[k] == ghost_old_v@[j]) &&
        (k == j ==> new_v@[k] == ghost_old_v@[i]) &&
        (k != i && k != j ==> new_v@[k] == ghost_old_v@[k])
    ) by {
        if k == i {
            assert(new_v@[k] == ghost_old_v@[j]);
        } else if k == j {
            assert(new_v@[k] == ghost_old_v@[i]);
        } else {
            assert(new_v@[k] == ghost_old_v@[k]);
        }
    };
}

proof fn lemma_bubble_pass_invariant(a: &Vec<i32>, i: usize, j: usize, ghost_old_a: Ghost<Seq<i32>>)
    requires
        0 <= i < a.len(),
        0 <= j <= i,
        ghost_old_a@ == old(a)@,
        forall|k: int| j <= k < i ==> a@[k] <= a@[k+1],
    ensures
        forall|k: int| j <= k < i ==> a@[k] <= a@[k+1],
{
    assert forall|k: int| j <= k < i implies a@[k] <= a@[k+1] by {
        assert(a@[k] <= a@[k+1]);
    };
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
fn bubble_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j],
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let mut i: usize = a.len();
    while i > 0
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int| i <= k < l < a.len() ==> a@[k] <= a@[l],
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut j: usize = 0;
        while j < i - 1
            invariant
                0 <= i <= a.len(),
                0 <= j < i,
                forall|k: int| 0 <= k < j ==> a@[k] <= a@[k+1],
                forall|k: int, l: int| i <= k < l < a.len() ==> a@[k] <= a@[l],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] > a[j + 1] {
                let ghost_old_a = Ghost(a@);
                a.swap(j, j + 1);
                proof {
                    lemma_swap_effects(a, j, j + 1, ghost_old_a);
                    lemma_swap_preserves_multiset(a, j, j + 1);
                }
            }
            j = j + 1;
        }
        i = i - 1;
    }
}
// </vc-code>

fn main() {
}

}