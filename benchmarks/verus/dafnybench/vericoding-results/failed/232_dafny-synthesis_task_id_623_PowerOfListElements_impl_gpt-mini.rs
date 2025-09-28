use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn power_of_list_elements(l: Vec<i32>, n: u32) -> (result: Vec<i32>)
    ensures 
        result.len() == l.len(),
        forall|i: int| #![auto] 0 <= i < l.len() ==> result[i] == power(l[i] as int, n as int),
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant i <= l.len();
        invariant res.len() == i;
        invariant forall|j: int| 0 <= j < (i as int) ==> res@[j] == power(l@[j] as int, n as int) as i32;
        decreases l.len() - i
    {
        let v: i32 = l@[i as int];
        let p: int = power(v as int, n as int);
        res.push(p as i32);
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}

}