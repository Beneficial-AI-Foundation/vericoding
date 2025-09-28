use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn identical_at_index(a: Seq<int>, b: Seq<int>, c: Seq<int>, i: int) -> bool
    recommends 0 <= i < a.len()
{
    a[i] == b[i] && b[i] == c[i]
}

proof fn identical_positions_same_as_set(a: Seq<int>, b: Seq<int>, c: Seq<int>, i: int)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        Set::<int>::new(|j: int| 0 <= j < a.len() && identical_at_index(a, b, c, j)).contains(i) == 
        (0 <= i < a.len() && identical_at_index(a, b, c, i))
{
    reveal_with_fuel(Set::new, 2);
}

proof fn set_len_lemma(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    ensures
        Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len() ==
        Set::<int>::new(|j: int| 0 <= j < a.len() && identical_at_index(a, b, c, j)).len()
{
    reveal_with_fuel(Set::new, 2);
}

proof fn set_extend_lemma(a: Seq<int>, b: Seq<int>, c: Seq<int>, idx: int)
    requires
        a.len() == b.len() && b.len() == c.len(),
        0 <= idx < a.len(),
        identical_at_index(a, b, c, idx),
    ensures
        Set::<int>::new(|i: int| 0 <= i < idx && identical_at_index(a, b, c, i)).insert(idx).len() ==
        Set::<int>::new(|i: int| 0 <= i < idx && identical_at_index(a, b, c, i)).len() + 1
{
    reveal_with_fuel(Set::new, 2);
}

proof fn set_preserve_lemma(a: Seq<int>, b: Seq<int>, c: Seq<int>, idx: int)
    requires
        a.len() == b.len() && b.len() == c.len(),
        0 <= idx < a.len(),
        !identical_at_index(a, b, c, idx),
    ensures
        Set::<int>::new(|i: int| 0 <= i < idx && identical_at_index(a, b, c, i)) ==
        Set::<int>::new(|i: int| 0 <= i < idx + 1 && identical_at_index(a, b, c, i))
{
    reveal_with_fuel(Set::new, 2);
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut idx: usize = 0;
    let len: usize = a.len();
    while idx < len
        invariant
            0 <= idx <= len,
            count >= 0,
            count == Set::<int>::new(|i: int| 0 <= i < idx as int && identical_at_index(a, b, c, i)).len(),
        decreases len - idx,
    {
        ghost {
            let idx_int: int = idx as int;
            assert(0 <= idx_int < a.len() as int);
        }
        if a[idx] == b[idx] && b[idx] == c[idx] {
            proof {
                let idx_int: int = idx as int;
                identical_positions_same_as_set(a, b, c, idx_int);
                set_extend_lemma(a, b, c, idx_int);
                let prev_set = Set::<int>::new(|i: int| 0 <= i < idx_int && identical_at_index(a, b, c, i));
                assert(prev_set.insert(idx_int).len() == count + 1);
            }
            count = count + 1;
        } else {
            proof {
                let idx_int: int = idx as int;
                set_preserve_lemma(a, b, c, idx_int);
            }
        }
        idx = idx + 1;
    }
    proof {
        set_len_lemma(a, b, c);
    }
    count
}
// </vc-code>

fn main() {
}

}