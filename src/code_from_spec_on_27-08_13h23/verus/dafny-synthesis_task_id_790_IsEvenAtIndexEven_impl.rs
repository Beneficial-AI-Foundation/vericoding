use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_even_at_index_even(lst: &Vec<i32>) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < lst.len() ==> (is_even(i) ==> is_even(lst[i] as int)))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_even_at_index_even(lst: &Vec<i32>) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < lst.len() ==> (is_even(i) ==> is_even(lst[i] as int)))
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i as int ==> (is_even(j) ==> is_even(lst[j as usize] as int))
    {
        if is_even(i as int) {
            if !is_even(lst[i] as int) {
                return false;
            }
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}