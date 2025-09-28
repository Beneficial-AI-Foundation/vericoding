// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed += operator for int type */
proof fn find_first_even(a: &Vec<i32>) -> (index: int)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
    ensures
        0 <= index < a.len(),
        is_even(a[index as int]),
        forall|k: int| 0 <= k < index ==> is_odd(a[k as int])
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_odd(a[k as int]),
            exists|k: int| i <= k < a.len() && is_even(a[k as int])
        decreases a.len() - i
    {
        if is_even(a[i as int]) {
            return i;
        }
        i = i + 1;
    }
    assert(false);
    0
}

/* helper modified by LLM (iteration 5): fixed += operator for int type */
proof fn find_first_odd(a: &Vec<i32>) -> (index: int)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures
        0 <= index < a.len(),
        is_odd(a[index as int]),
        forall|k: int| 0 <= k < index ==> is_even(a[k as int])
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_even(a[k as int]),
            exists|k: int| i <= k < a.len() && is_odd(a[k as int])
        decreases a.len() - i
    {
        if is_odd(a[i as int]) {
            return i;
        }
        i = i + 1;
    }
    assert(false);
    0
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated iteration number */
{
    let mut even_index: Option<usize> = None;
    let mut odd_index: Option<usize> = None;
    for i in 0..a.len() {
        if even_index.is_none() && a[i] % 2 == 0 {
            even_index = Some(i);
        }
        if odd_index.is_none() && a[i] % 2 != 0 {
            odd_index = Some(i);
        }
        if even_index.is_some() && odd_index.is_some() {
            break;
        }
    }
    let even_index = even_index.unwrap();
    let odd_index = odd_index.unwrap();
    a[even_index] - a[odd_index]
}
// </vc-code>

}
fn main() {}