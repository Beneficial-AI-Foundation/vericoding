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
proof fn lemma_recursive_positive_product_unfold(q: Seq<int>, i: nat)
    requires
        i <= q.len(),
    ensures
        recursive_positive_product(q.subrange(i as int, q.len() as int)) == 
        if i == q.len() {
            1
        } else if q[i as int] <= 0 {
            recursive_positive_product(q.subrange((i + 1) as int, q.len() as int))
        } else {
            q[i as int] * recursive_positive_product(q.subrange((i + 1) as int, q.len() as int))
        }
    decreases q.len() - i
{
    if i == q.len() {
        assert(q.subrange(i as int, q.len() as int).len() == 0);
    } else {
        assert(q.subrange(i as int, q.len() as int)[0] == q[i as int]);
        assert(q.subrange(i as int, q.len() as int).subrange(1, q.subrange(i as int, q.len() as int).len() as int) 
               =~= q.subrange((i + 1) as int, q.len() as int));
    }
}

proof fn lemma_recursive_count_unfold(key: int, q: Seq<int>, i: nat)
    requires
        i <= q.len(),
    ensures
        recursive_count(key, q.subrange(0, i as int)) ==
        if i == 0 {
            0
        } else if q[i - 1] == key {
            1 + recursive_count(key, q.subrange(0, i as int - 1))
        } else {
            recursive_count(key, q.subrange(0, i as int - 1))
        }
    decreases i
{
    if i == 0 {
        assert(q.subrange(0, i as int).len() == 0);
    } else {
        assert(q.subrange(0, i as int)[q.subrange(0, i as int).len() - 1] == q[i - 1]);
        assert(q.subrange(0, i as int).subrange(0, q.subrange(0, i as int).len() as int - 1)
               =~= q.subrange(0, i as int - 1));
    }
}

proof fn lemma_push_subrange(q: Seq<int>, i: nat)
    requires
        i < q.len(),
    ensures
        q.subrange(0, i as int).push(q[i as int]) =~= q.subrange(0, (i + 1) as int),
{
    assert forall |j: int| 0 <= j < i + 1 implies 
        #[trigger] q.subrange(0, i as int).push(q[i as int])[j] == q.subrange(0, (i + 1) as int)[j] by {
        if j < i {
            assert(q.subrange(0, i as int).push(q[i as int])[j] == q.subrange(0, i as int)[j]);
            assert(q.subrange(0, i as int)[j] == q[j]);
            assert(q.subrange(0, (i + 1) as int)[j] == q[j]);
        } else {
            assert(j == i);
            assert(q.subrange(0, i as int).push(q[i as int])[j] == q[i as int]);
            assert(q.subrange(0, (i + 1) as int)[j] == q[j]);
        }
    }
}

proof fn lemma_recursive_positive_product_step(q: Seq<int>, i: nat)
    requires
        i < q.len(),
    ensures
        recursive_positive_product(q.subrange(0, (i + 1) as int)) ==
        if q[i as int] <= 0 {
            recursive_positive_product(q.subrange(0, i as int))
        } else {
            recursive_positive_product(q.subrange(0, i as int)) * q[i as int]
        }
{
    lemma_push_subrange(q, i as nat);
    let q_up_to_i_plus_1 = q.subrange(0, (i + 1) as int);
    let q_up_to_i = q.subrange(0, i as int);
    
    assert(q_up_to_i_plus_1 =~= q_up_to_i.push(q[i as int]));
    
    lemma_recursive_positive_product_unfold(q_up_to_i_plus_1, 0);
    
    if q_up_to_i_plus_1.len() > 0 {
        if q_up_to_i_plus_1[0] <= 0 {
            assert(recursive_positive_product(q_up_to_i_plus_1) == 
                   recursive_positive_product(q_up_to_i_plus_1.subrange(1, q_up_to_i_plus_1.len() as int)));
        } else {
            assert(recursive_positive_product(q_up_to_i_plus_1) == 
                   q_up_to_i_plus_1[0] * recursive_positive_product(q_up_to_i_plus_1.subrange(1, q_up_to_i_plus_1.len() as int)));
        }
    }
    
    if i == 0 {
        assert(q_up_to_i.len() == 0);
        assert(recursive_positive_product(q_up_to_i) == 1);
        assert(q_up_to_i_plus_1[0] == q[0]);
        if q[0] <= 0 {
            assert(recursive_positive_product(q_up_to_i_plus_1) == 1);
        } else {
            assert(recursive_positive_product(q_up_to_i_plus_1) == q[0]);
        }
    } else {
        lemma_recursive_positive_product_append(q_up_to_i, q[i as int]);
    }
}

proof fn lemma_recursive_positive_product_append(s: Seq<int>, elem: int)
    ensures
        recursive_positive_product(s.push(elem)) ==
        if elem <= 0 {
            recursive_positive_product(s)
        } else {
            recursive_positive_product(s) * elem
        }
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(elem)[0] == elem);
        assert(s.push(elem).subrange(1, s.push(elem).len() as int).len() == 0);
    } else {
        assert(s.push(elem)[0] == s[0]);
        assert(s.push(elem).subrange(1, s.push(elem).len() as int) =~= s.subrange(1, s.len() as int).push(elem));
        
        if s[0] <= 0 {
            lemma_recursive_positive_product_append(s.subrange(1, s.len() as int), elem);
        } else {
            lemma_recursive_positive_product_append(s.subrange(1, s.len() as int), elem);
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
    let mut prod: i32 = 1;
    let mut count: u32 = 0;
    let ghost q_seq = q@.map(|_, x: i32| x as int);
    
    for i in 0..q.len()
        invariant
            prod == recursive_positive_product(q_seq.subrange(0, i as int)),
            count == recursive_count(key as int, q_seq.subrange(0, i as int)) as u32,
            i <= q.len(),
            q_seq =~= q@.map(|_, x: i32| x as int),
    {
        // Handle product calculation
        proof {
            lemma_push_subrange(q_seq, i as nat);
            lemma_recursive_count_unfold(key as int, q_seq.subrange(0, (i + 1) as int), (i + 1) as nat);
            lemma_recursive_positive_product_step(q_seq, i as nat);
        }
        
        if q[i] > 0 {
            prod = prod * q[i];
        }
        
        if q[i] == key {
            count = count + 1;
        }
    }
    
    proof {
        assert(q_seq.subrange(0, q.len() as int) =~= q_seq);
    }
    
    (prod, count)
}
// </vc-code>

fn main() {}

}