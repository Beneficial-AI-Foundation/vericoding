// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}

fn count_exec(a: &Vec<i8>, x: i8) -> (c: u64)
    ensures
        c as int == count_rec(a@.map(|_i: int, v: i8| v as int), x as int),
{
    let mut i: usize = 0;
    let mut c: u64 = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c as int == count_rec(a@.subrange(0, i as int).map(|_i: int, v: i8| v as int), x as int),
        decreases a.len() - i
    {
        if a[i] == x {
            c = c + 1;
        }
        i = i + 1;
    }
    c
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
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@ == old(a)@,
            forall|k: int| 0 <= k < result@.len() ==> 
                count_rec(a@.map(|_idx: int, x: i8| x as int), result@[k] as int) == 1,
            forall|j: int| 0 <= j < i ==> 
                (result@.map(|_idx: int, x: i8| x as int).contains(a@[j] as int) <==>
                 count_rec(a@.map(|_idx: int, x: i8| x as int), a@[j] as int) == 1),
        decreases a.len() - i
    {
        let current_val = a[i];
        let count = count_exec(&a, current_val);
        if count == 1 {
            result.push(current_val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}