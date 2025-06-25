// ATOM 

pub open spec fn isPeek(v: &[int], i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

// ATOM 

pub open spec fn peekSum(v: &[int], i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i
{
    if i == 0 {
        0
    } else if isPeek(v, i - 1) {
        v[i - 1] + peekSum(v, i - 1)
    } else {
        peekSum(v, i - 1)
    }
}

// SPEC 

pub fn mPeekSum(v: &[int]) -> (sum: int)
    requires(v.len() > 0)
    ensures(sum == peekSum(v, v.len() as int))
{
}