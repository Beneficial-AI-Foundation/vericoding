use vstd::prelude::*;

verus! {

spec fn recursive_positive_product(q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        1
    } else if q[0] <= 0 {
        recursive_positive_product(q.subrange(1, q.len() as int))
    } else {
        q[0] * recursive_positive_product(q.subrange(1, q.len() as int))
    }
}

spec fn recursive_count(key: int, q: Seq<int>) -> int
    decreases q.len()
{
    if q.len() == 0 {
        0
    } else if q[q.len() - 1] == key {
        1 + recursive_count(key, q.subrange(0, q.len() as int - 1))
    } else {
        recursive_count(key, q.subrange(0, q.len() as int - 1))
    }
}

spec fn county(elem: int, key: int) -> int {
    if elem == key { 1 } else { 0 }
}

spec fn prody(elem: int) -> int {
    if elem <= 0 { 1 } else { elem }
}

// <vc-helpers>
proof fn lemma_map_subrange<T, U>(s: Seq<T>, f: spec_fn(nat, T) -> U, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures s.subrange(start, end).map(f) == s.map(f).subrange(start, end)
    decreases end - start
{
    if start == end {
        assert(s.subrange(start, end) == Seq::<T>::empty());
        assert(s.map(f).subrange(start, end) == Seq::<U>::empty());
    } else {
        lemma_map_subrange(s, f, start + 1, end);
    }
}

proof fn lemma_recursive_positive_product_loop(q: Seq<int>, i: int, product: int)
    requires 0 <= i <= q.len()
    requires product == recursive_positive_product(q.subrange(0, i))
    ensures product * recursive_positive_product(q.subrange(i, q.len() as int)) == recursive_positive_product(q)
    decreases q.len() - i
{
    if i == q.len() {
        assert(q.subrange(i, q.len() as int) == Seq::<int>::empty());
        assert(recursive_positive_product(q.subrange(i, q.len() as int)) == 1);
        assert(q.subrange(0, i) == q);
    } else {
        if q[i] <= 0 {
            lemma_recursive_positive_product_loop(q, i + 1, product);
            assert(recursive_positive_product(q.subrange(i, q.len() as int)) == 
                   recursive_positive_product(q.subrange(i + 1, q.len() as int)));
        } else {
            lemma_recursive_positive_product_loop(q, i + 1, product * q[i]);
            assert(recursive_positive_product(q.subrange(i, q.len() as int)) == 
                   q[i] * recursive_positive_product(q.subrange(i + 1, q.len() as int)));
        }
    }
}

proof fn lemma_recursive_count_loop(q: Seq<int>, key: int, i: int, count: int)
    requires 0 <= i <= q.len()
    requires count == recursive_count(key, q.subrange(i, q.len() as int))
    ensures count + recursive_count(key, q.subrange(0, i)) == recursive_count(key, q)
    decreases i
{
    if i == 0 {
        assert(q.subrange(0, i) == Seq::<int>::empty());
        assert(recursive_count(key, q.subrange(0, i)) == 0);
        assert(q.subrange(i, q.len() as int) == q);
    } else {
        if q[i - 1] == key {
            lemma_recursive_count_loop(q, key, i - 1, count + 1);
            assert(recursive_count(key, q.subrange(0, i)) == 
                   1 + recursive_count(key, q.subrange(0, i - 1)));
        } else {
            lemma_recursive_count_loop(q, key, i - 1, count);
            assert(recursive_count(key, q.subrange(0, i)) == 
                   recursive_count(key, q.subrange(0, i - 1)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn prod_and_count(q: &[i32], key: i32) -> (i32, u32)
    ensures |result: (i32, u32)| 
        result.0 == recursive_positive_product(q@.map(|_, x: i32| x as int)) &&
        result.1 == recursive_count(key as int, q@.map(|_, x: i32| x as int)) as u32
// </vc-spec>
// <vc-code>
{
    let mut product: i32 = 1;
    let mut count: u32 = 0;
    
    let ghost q_spec = q@.map(|_, x: i32| x as int);
    
    for i in 0..q.len()
        invariant
            product == recursive_positive_product(q_spec.subrange(0, i as int)),
            count == recursive_count(key as int, q_spec.subrange(i as int, q_spec.len())) as u32,
            q_spec == q@.map(|_, x: i32| x as int),
            q_spec.len() == q@.len()
    {
        if q[i] > 0 {
            product = product * q[i];
        }
        
        if q[i] == key {
            count = count + 1;
        }
        
        proof {
            assert(q_spec.subrange(0, i as int + 1) == q_spec.subrange(0, i as int).push(q_spec[i as int]));
            assert(q_spec.subrange(i as int + 1, q_spec.len()) == q_spec.subrange(i as int, q_spec.len()).subrange(1, q_spec.subrange(i as int, q_spec.len()).len()));
        }
    }
    
    proof {
        lemma_recursive_positive_product_loop(q_spec, 0, 1);
        lemma_recursive_count_loop(q_spec, key as int, q.len() as int, 0);
        assert(q_spec.subrange(0, q.len() as int) == q_spec);
        assert(q_spec.subrange(q.len() as int, q_spec.len()) == Seq::<int>::empty());
    }
    
    (product, count)
}
// </vc-code>

fn main() {}

}