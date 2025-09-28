// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added count_val helper to compute counts without using Map to avoid spec issues */
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}

fn count_val(val: i8, a: &Vec<i8>) -> usize
    ensures
        count == count_rec(a@.map(|_i: int, x: i8| x as int), val as int)
{
    let mut count: usize = 0;
    let mut j: usize = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            count as int == count_rec(a@.subrange(0, j as int).map(|_i: int, x: i8| x as int), val as int)
        decreases a.len() - j
    {
        if a[j] == val {
            count += 1;
        }
        j += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < a@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) >= 1
    ensures 
        forall|i: int| 0 <= i < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[i] as int) == 1,
        forall|i: int| 0 <= i < a@.len() ==> (result@.map(|_i: int, x: i8| x as int).contains(a@[i] as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) == 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented remove_duplicates using count_val to check for unique elements */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall |j: int| 0 <= j < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[j] as int) == 1,
            forall |j: int| 0 <= j < result@.len() ==> result@.map(|_i: int, x: i8| x as int).contains(result@[j] as int),
            forall |j: int| 0 <= j < i ==> a@[j] in result@.map(|_i: int, x: i8| x as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[j] as int) == 1 && result@.map(|_i: int, x: i8| x as int).contains(a@[j] as int)
        decreases a.len() - i
    {
        let val = a[i];
        let c = count_val(val, &a);
        if c == 1 {
            result.push(val);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}