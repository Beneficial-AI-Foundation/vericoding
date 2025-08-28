use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let min_prefix = min(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max(a: Seq<int>) -> int
    recommends a.len() > 0  
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let max_prefix = max(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
proof fn lemma_min_max_single_element(a: Seq<int>)
    requires a.len() == 1
    ensures min(a) == a[0] && max(a) == a[0]
{
}

proof fn lemma_min_properties(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> min(a) <= a[i]
    decreases a.len()
{
    if a.len() == 1 {
        lemma_min_max_single_element(a);
    } else {
        let prefix = a.take(a.len() - 1);
        lemma_min_properties(prefix);
        assert(forall|i: int| 0 <= i < prefix.len() ==> min(prefix) <= prefix[i]);
        assert(forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == a[i]);
    }
}

proof fn lemma_max_properties(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> max(a) >= a[i]
    decreases a.len()
{
    if a.len() == 1 {
        lemma_min_max_single_element(a);
    } else {
        let prefix = a.take(a.len() - 1);
        lemma_max_properties(prefix);
        assert(forall|i: int| 0 <= i < prefix.len() ==> max(prefix) >= prefix[i]);
        assert(forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == a[i]);
    }
}

proof fn lemma_min_max_extend(prefix: Seq<int>, elem: int)
    requires prefix.len() > 0
    ensures min(prefix.push(elem)) == if elem <= min(prefix) { elem } else { min(prefix) }
    ensures max(prefix.push(elem)) == if elem >= max(prefix) { elem } else { max(prefix) }
{
    let extended = prefix.push(elem);
    assert(extended.take(extended.len() - 1) == prefix);
    assert(extended[extended.len() - 1] == elem);
}

proof fn lemma_min_max_bounds()
    ensures forall|x: i32, y: i32| x as int - y as int >= i32::MIN as int
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    
    let mut i = 1;
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            min_val as int == min(a@.take(i as int).map(|j, x| x as int)),
            max_val as int == max(a@.take(i as int).map(|j, x| x as int))
        decreases a.len() - i
    {
        proof {
            let prev_seq = a@.take(i as int).map(|j, x| x as int);
            let next_seq = a@.take((i + 1) as int).map(|j, x| x as int);
            assert(next_seq == prev_seq.push(a[i] as int));
            lemma_min_max_extend(prev_seq, a[i] as int);
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    proof {
        assert(a@.take(a.len() as int) == a@);
        assert(a@.map(|j, x| x as int).take(a.len() as int) == a@.map(|j, x| x as int));
        lemma_min_max_bounds();
    }
    
    ((max_val as int) - (min_val as int)) as i32
}
// </vc-code>

fn main() {}

}