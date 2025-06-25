use vstd::prelude::*;

verus! {

pub fn unique_product(arr: &[int]) -> (product: int)
    ensures
        product == set_product(Set::new(|i: int| 0 <= i < arr.len() ==> arr[i as usize]))
{
}

spec fn set_product(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        let x = s.choose();
        x * set_product(s.remove(x))
    }
}

proof fn set_product_lemma(s: Set<int>, x: int)
    requires
        s.contains(x)
    ensures
        set_product(s.remove(x)) * x == set_product(s)
    decreases s.len()
{
}

}