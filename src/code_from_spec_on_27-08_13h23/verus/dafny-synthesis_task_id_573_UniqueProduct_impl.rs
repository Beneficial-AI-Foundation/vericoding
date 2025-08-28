use vstd::prelude::*;

verus! {

spec fn set_product(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        arbitrary()  // This represents the nondeterministic choice like |:| in Dafny
    }
}

// <vc-helpers>
spec fn compute_product(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        let x = choose|x: int| s.contains(x);
        x * compute_product(s.remove(x))
    }
}

proof fn set_product_equals_compute_product(s: Set<int>)
    ensures set_product(s) == compute_product(s)
    decreases s.len()
{
    if s.is_empty() {
        assert(set_product(s) == 1);
        assert(compute_product(s) == 1);
    } else {
        let x = choose|x: int| s.contains(x);
        assert(set_product(s) == x * set_product(s.remove(x)));
        assert(compute_product(s) == x * compute_product(s.remove(x)));
        set_product_equals_compute_product(s.remove(x));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn unique_product(arr: &[i32]) -> (product: i32)
    ensures product == set_product(arr@.to_set().map(|x: i32| x as int))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn unique_product(arr: &[i32]) -> (product: i32)
    ensures product == set_product(arr@.to_set().map(|x: i32| x as int))
{
    let mut prod: i32 = 1;
    let mut i: usize = 0;
    let set = arr@.to_set().map(|x: i32| x as int);
    
    proof {
        set_product_equals_compute_product(set);
    }
    
    let mut seen = Set::empty();
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            prod as int == compute_product(set.intersection(seen)),
            seen.subset_of(set)
        decreases arr.len() - i
    {
        if !seen.contains(arr@[i] as int) {
            prod = prod * arr@[i];
            seen = seen.insert(arr@[i] as int);
        }
        i = i + 1;
    }
    
    proof {
        assert(seen == set) by {
            assert forall|x: int| set.contains(x) implies seen.contains(x) by {
                assert(arr@.to_set().contains(x as i32));
                assert(exists|i: int| 0 <= i < arr.len() && arr@[i] == (x as i32));
                let j = choose|i: int| 0 <= i < arr.len() && arr@[i] == (x as i32);
                assert(seen.contains(x));
            };
        };
        assert(prod as int == compute_product(set));
    }
    
    prod
}
// </vc-code>

fn main() {}

}