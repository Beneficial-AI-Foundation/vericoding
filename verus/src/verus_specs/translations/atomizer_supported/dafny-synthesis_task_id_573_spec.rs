use vstd::prelude::*;

verus! {

pub fn UniqueProduct(arr: &[int]) -> (product: int)
    ensures product == SetProduct(Set::new(|i: int| 0 <= i < arr.len() ==> arr[i as usize]))
{
}

spec fn SetProduct(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        let x = s.choose();
        x * SetProduct(s.remove(x))
    }
}

proof fn SetProductLemma(s: Set<int>, x: int)
    requires x in s
    ensures SetProduct(s.remove(x)) * x == SetProduct(s)
    decreases s.len()
{
    if !s.is_empty() {
        let y = s.choose();
        if y == x {
        } else {
            SetProductLemma(s.remove(y), x);
            SetProductLemma(s.remove(x), y);
        }
    }
}

}