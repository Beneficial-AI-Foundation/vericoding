use vstd::prelude::*;

verus! {

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> (is_odd(j) ==> is_odd(a[j as int])),
    {
        if i % 2 == 1 {  // Check if index is odd using usize arithmetic
            proof {
                let i_as_int: int = i as int;
                assert(i_as_int % 2 == 1);
                assert(is_odd(i_as_int));  // Connect usize check to spec function
            }
            if a[i] % 2 != 1 {  // Check if value at odd index is odd
                proof {
                    let i_as_int: int = i as int;
                    assert(a[i_as_int] % 2 != 1);
                    assert(!is_odd(a[i_as_int]));
                    assert(is_odd(i_as_int) && !is_odd(a[i_as_int]));
                    assert(!(forall|k: int| 0 <= k < a.len() ==> (is_odd(k) ==> is_odd(a[k]))));
                }
                return false;
            }
            proof {
                let i_as_int: int = i as int;
                assert(a[i_as_int] % 2 == 1);
                assert(is_odd(a[i_as_int]));
            }
        }
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> (is_odd(j) ==> is_odd(a[j as int])));
    }
    true
}
// </vc-code>

fn main() {
}

}