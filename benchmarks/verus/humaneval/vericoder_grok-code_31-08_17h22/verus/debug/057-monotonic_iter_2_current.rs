use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_non_dec(l: &Vec<i32>) -> (ret: bool)
    ensures
        ret <==> forall |i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)
{
    let mut i = 0;
    while i + 1 < l.len()
        invariant
            0 <= i <= l.len() - 1 &&
            (forall |k: int| #![trigger] 0 <= k < i ==> l@.index(k) <= l@.index(k + 1))
    {
        if l[i] > l[i + 1] {
            return false;
        }
        i += 1;
    }
    _proof {
        assert(forall |i_: int, j: int| (0 <= i_ && i_ < j && j < l@.len()) ==> l@.index(i_) <= l@.index(j));
    }
    return true;
}

fn is_non_inc(l: &Vec<i32>) -> (ret: bool)
    ensures
        ret <==> forall |i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)
{
    let mut i = 0;
    while i + 1 < l.len()
        invariant
            0 <= i <= l.len() - 1 &&
            (forall |k: int| #![trigger] 0 <= k < i ==> l@.index(k) >= l@.index(k + 1))
    {
        if l[i] < l[i + 1] {
            return false;
        }
        i += 1;
    }
    _proof {
        assert(forall |i_: int, j: int| (0 <= i_ && i_ < j && j < l@.len()) ==> l@.index(i_) >= l@.index(j));
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let l_view = l@;
    if is_non_dec(&l) {
        return true;
    } else {
        return is_non_inc(&l);
    }
}
// </vc-code>

fn main() {}
}