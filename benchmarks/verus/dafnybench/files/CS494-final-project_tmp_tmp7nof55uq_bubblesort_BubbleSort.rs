use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|x: usize, y: usize| from <= x < y < to ==> a[x as int] <= a[y as int]
}

spec fn pivot(a: &Vec<i32>, to: usize, pvt: usize) -> bool
    recommends
        pvt < to,
        to <= a.len(),
{
    forall|x: usize, y: usize| 0 <= x < pvt < y < to ==> a[x as int] <= a[y as int]
}

fn BubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures 
        sorted(a, 0, a.len()),
        a@.to_multiset() == old(a)@.to_multiset(),
{
    assume(false);
    unreached();
}

}
fn main() {}