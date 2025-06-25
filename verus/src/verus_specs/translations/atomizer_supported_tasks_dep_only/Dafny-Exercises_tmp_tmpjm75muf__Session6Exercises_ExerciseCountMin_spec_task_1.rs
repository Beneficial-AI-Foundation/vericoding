use vstd::prelude::*;

verus! {

spec fn min(v: &[int], i: int) -> int
    recommends
        1 <= i <= v.len(),
    ensures |result: int|
        forall|k: int| 0 <= k < i ==> v[k] >= result,
{
    if i == 1 {
        v[0]
    } else if v[(i-1) as usize] <= min(v, i-1) {
        v[(i-1) as usize]
    } else {
        min(v, i-1)
    }
}

spec fn countMin(v: &[int], x: int, i: int) -> int
    recommends
        0 <= i <= v.len(),
    ensures |result: int|
        !v.subrange(0, i as usize).contains(x) ==> result == 0,
{
    if i == 0 {
        0
    } else if v[(i-1) as usize] == x {
        1 + countMin(v, x, i-1)
    } else {
        countMin(v, x, i-1)
    }
}

pub fn mCountMin(v: &[int]) -> (c: int)
    requires
        v.len() > 0,
    ensures
        c == countMin(v, min(v, v.len() as int), v.len() as int),
{
}

}