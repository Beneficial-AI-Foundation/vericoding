use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_even_at_index_even(lst: &Vec<i32>) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < lst.len() ==> (is_even(i) ==> is_even(lst[i] as int)))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> (is_even(j) ==> is_even(lst@[j] as int)),
        decreases lst.len() - i,
    {
        if i % 2 == 0 {  // Check if index is even using executable code
            if lst[i] % 2 != 0 {
                proof {
                    assert(is_even(i as int));  // i % 2 == 0 implies is_even(i)
                    assert(!is_even(lst@[i as int] as int));  // lst[i] % 2 != 0 implies !is_even(lst[i])
                    assert(!forall|j: int| 0 <= j < lst@.len() ==> (is_even(j) ==> is_even(lst@[j] as int)));
                }
                return false;
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(i == lst@.len());
        assert(forall|j: int| 0 <= j < lst@.len() ==> (is_even(j) ==> is_even(lst@[j] as int)));
    }
    true
}
// </vc-code>

fn main() {
}

}