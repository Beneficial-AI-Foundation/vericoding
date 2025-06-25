use vstd::prelude::*;

verus! {

pub fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires(a.len() > 0)
    ensures(diff == max(a@) - min(a@))
{
}

pub open spec fn min(a: Seq<i32>) -> i32
    recommends(a.len() > 0)
{
    if a.len() == 1 {
        a[0]
    } else {
        let min_prefix = min(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min(a.subrange(0, a.len() - 1))
        }
    }
}

pub open spec fn max(a: Seq<i32>) -> i32
    recommends(a.len() > 0)
{
    if a.len() == 1 {
        a[0]
    } else {
        let max_prefix = max(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max(a.subrange(0, a.len() - 1))
        }
    }
}

}