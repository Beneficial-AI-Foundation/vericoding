use vstd::prelude::*;

verus! {

spec fn gcd_int_spec(a: int, b: int) -> int
    decreases (if a >= 0 && b >= 0 { a + b } else { 0 }) as nat,
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b && a > 0 && b > 0 {
        gcd_int_spec(a, b - a)
    } else if a > b && a > 0 && b > 0 {
        gcd_int_spec(a - b, b)
    } else {
        0
    }
}

fn gcd_int_exec(a: u32, b: u32) -> (result: u32)
    ensures
        result >= 0,
        result == gcd_int_spec(a as int, b as int),
        a == 0 && b == 0 ==> result == 0,
        a > 0 ==> result > 0,
        b > 0 ==> result > 0,
    decreases a + b,
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd_int_exec(a, b - a)
    } else {
        gcd_int_exec(a - b, b)
    }
}

fn gcd(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 0 && b[i] >= 0,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> gcd_int_spec(a[i] as int, b[i] as int) == res[i] as int,
{
    let mut res = Vec::with_capacity(a.len());
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            res.len() == idx,
            a.len() == b.len(),
            forall|j: int| 0 <= j < idx ==> gcd_int_spec(a[j] as int, b[j] as int) == res[j] as int,
        decreases a.len() - idx,
    {
        assert(idx < a.len());
        assert(idx < b.len());
        let gcd_result = gcd_int_exec(a[idx], b[idx]);
        res.push(gcd_result);
        idx += 1;
    }
    res
}

}