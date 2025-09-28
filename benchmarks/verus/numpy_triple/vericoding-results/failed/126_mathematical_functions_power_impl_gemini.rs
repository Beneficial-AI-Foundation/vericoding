// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn pow(base: int, exp: int) -> int
    decreases if exp >= 0 { exp } else { -exp }
{
    if exp < 0 {
        0
    } else if exp == 0 {
        1
    } else {
        base * pow(base, exp - 1)
    }
}

fn power_exec(base: i8, exp: i8) -> (res: i8)
    requires
        base == 0 ==> exp >= 0,
        -128 <= pow(base as int, exp as int) <= 127,
    ensures
        res as int == pow(base as int, exp as int),
{
    let b = base as int;
    let e = exp as int;
    if e < 0 {
        return 0;
    }
    let mut res: int = 1;
    let mut i: int = 0;
    while i < e
        invariant
            0 <= i <= e,
            res == pow(b, i),
    {
        res = res * b;
        i = i + 1;
    }
    res as i8
}
// </vc-helpers>

// <vc-spec>
fn numpy_power(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1@.len() ==> {
            (x1[i] == 0 ==> x2[i] as int >= 0)
        },
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            (x2[i] as int == 0 && x1[i] as int != 0 ==> result[i] as int == 1) &&
            (x2[i] as int == 1 ==> result[i] as int == x1[i] as int) &&
            (x1[i] as int > 1 && x2[i] as int > 0 ==> result[i] as int > x1[i] as int)
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == pow(x1@[j] as int, x2@[j] as int),
        decreases x1.len() - i,
    {
        let b = x1[i];
        let e = x2[i];
        
        let val = power_exec(b, e);
        
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}