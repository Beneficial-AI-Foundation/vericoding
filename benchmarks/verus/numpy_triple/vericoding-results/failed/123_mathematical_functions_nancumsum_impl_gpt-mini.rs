// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn cum_int(a: Vec<i8>) -> (result: Vec<int>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] == result[i-1] + a[i] as int,
{
    let mut res: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            i <= a.len(),
        decreases a.len() - i
    {
        if i == 0 {
            res.push(a[0] as int);
        } else {
            let prev = res[i-1];
            res.push(prev + (a[i] as int));
        }
        i += 1;
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
{
    // impl-start
    let cum = cum_int(a);
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < cum.len()
        invariant
            res.len() == i,
            i <= cum.len(),
        decreases cum.len() - i
    {
        res.push(cum[i] as i8);
        i += 1;
    }
    res
    // impl-end
}

// </vc-code>


}
fn main() {}