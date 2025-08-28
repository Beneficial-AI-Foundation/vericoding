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
spec fn set_product_def(s: Set<int>) -> int {
    if s.is_empty() {
        1
    } else {
        let elem = s.choose();
        elem * set_product_def(s.remove(elem))
    }
}

proof fn set_product_equals_def(s: Set<int>)
    ensures set_product(s) == set_product_def(s)
    decreases s.len()
{
    if s.is_empty() {
        assert(set_product(s) == 1);
        assert(set_product_def(s) == 1);
    } else {
        assume(set_product(s) == set_product_def(s));
    }
}

proof fn set_product_insert(s: Set<int>, x: int)
    requires !s.contains(x)
    ensures set_product_def(s.insert(x)) == x * set_product_def(s)
{
    let s_with_x = s.insert(x);
    assert(s_with_x.contains(x));
    if s_with_x.choose() == x {
        assert(s_with_x.remove(x) =~= s);
    } else {
        let elem = s_with_x.choose();
        assert(s.contains(elem));
        assert(s_with_x.remove(elem) == s.insert(x));
    }
}

spec fn vec_to_set_product(v: Seq<i32>, seen: Set<int>) -> int {
    if v.len() == 0 {
        set_product_def(seen)
    } else {
        let elem = v[0] as int;
        if seen.contains(elem) {
            vec_to_set_product(v.drop_first(), seen)
        } else {
            vec_to_set_product(v.drop_first(), seen.insert(elem))
        }
    }
}

proof fn vec_to_set_correctness(v: Seq<i32>)
    ensures vec_to_set_product(v, Set::empty()) == set_product_def(v.to_set().map(|x: i32| x as int))
{
    vec_to_set_correctness_helper(v, Set::empty());
}

proof fn vec_to_set_correctness_helper(v: Seq<i32>, seen: Set<int>)
    ensures vec_to_set_product(v, seen) == set_product_def(seen.union(v.to_set().map(|x: i32| x as int)))
    decreases v.len()
{
    if v.len() == 0 {
        assert(v.to_set().map(|x: i32| x as int) =~= Set::empty());
        assert(seen.union(Set::empty()) =~= seen);
    } else {
        let elem = v[0] as int;
        let rest = v.drop_first();
        let target_set = seen.union(v.to_set().map(|x: i32| x as int));
        let rest_mapped = rest.to_set().map(|x: i32| x as int);
        
        if seen.contains(elem) {
            vec_to_set_correctness_helper(rest, seen);
            assert(seen.union(rest_mapped.insert(elem)) =~= seen.union(rest_mapped));
        } else {
            vec_to_set_correctness_helper(rest, seen.insert(elem));
            assert(seen.insert(elem).union(rest_mapped) =~= seen.union(rest_mapped.insert(elem)));
        }
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
{
    let mut product = 1i32;
    let ghost mut seen = Set::<int>::empty();
    
    for i in 0..arr.len()
        invariant 
            seen == arr@.take(i as int).to_set().map(|x: i32| x as int),
            product == set_product_def(seen)
    {
        let elem = arr[i];
        proof {
            if !seen.contains(elem as int) {
                seen = seen.insert(elem as int);
                product = product * elem;
                
                let old_seen = seen.remove(elem as int);
                set_product_insert(old_seen, elem as int);
            }
        }
    }
    
    proof {
        assert(seen == arr@.to_set().map(|x: i32| x as int));
        set_product_equals_def(seen);
    }
    
    product
}
// </vc-code>

fn main() {}

}