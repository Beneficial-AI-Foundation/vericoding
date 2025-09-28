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
proof fn lemma_min_max_nonempty(a: Seq<int>)
    requires a.len() > 0,
    ensures min(a) <= max(a)
    decreases a.len()
{
    if a.len() == 1 {
        assert(min(a) == a[0]);
        assert(max(a) == a[0]);
    } else {
        let prefix = a.take(a.len() - 1);
        lemma_min_max_nonempty(prefix);
        assert(min(a) == if a[a.len() - 1] <= min(prefix) { a[a.len() - 1] } else { min(prefix) });
        assert(max(a) == if a[a.len() - 1] >= max(prefix) { a[a.len() - 1] } else { max(prefix) });
        assert(min(prefix) <= max(prefix));
        assert(a[a.len() - 1] <= max(a));
        assert(min(a) <= max(a));
    }
}

proof fn lemma_min_prefix(s: Seq<int>, i: int)
    requires 0 <= i <= s.len()
    ensures s.take(i).len() == i
    decreases s.len()
{
    if i == 0 {
        assert(s.take(0).len() == 0);
    } else if s.len() == 0 {
        // then i must be 0, already handled
    } else {
        // s.len() > 0 and i>0
        if i == s.len() {
            assert(s.take(i) == s);
            assert(s.take(i).len() == s.len());
            assert(s.len() == i);
        } else {
            // i < s.len()
            lemma_min_prefix(s.take(s.len()-1), i);
            assert(s.take(i) == s.take(s.len()-1).take(i));
            assert(s.take(i).len() == i);
        }
    }
}

proof fn lemma_push_min(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures min(s.push(x)) == if x <= min(s) { x } else { min(s) }
    decreases s.len()
{
    if s.len() == 1 {
        assert(min(s.push(x)) == if x <= s[0] { x } else { s[0] });
    } else {
        let prefix = s.take(s.len() - 1);
        lemma_push_min(prefix, x);
        lemma_push_min(prefix, s[s.len() - 1]);
        assert(s.push(x) == prefix.push(s[s.len() - 1]).push(x));
    }
}

proof fn lemma_push_max(s: Seq<int>, x: int)
    requires s.len() > 0
    ensures max(s.push(x)) == if x >= max(s) { x } else { max(s) }
    decreases s.len()
{
    if s.len() == 1 {
        assert(max(s.push(x)) == if x >= s[0] { x } else { s[0] });
    } else {
        let prefix = s.take(s.len() - 1);
        lemma_push_max(prefix, x);
        lemma_push_max(prefix, s[s.len() - 1]);
        assert(s.push(x) == prefix.push(s[s.len() - 1]).push(x));
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let a_int = a@.map(|x| x as int);
    let mut min_val = a_int[0];
    let mut max_val = a_int[0];
    
    let mut i = 1;
    while i < a_int.len()
        invariants
            min_val == min(a_int.take(i as int)),
            max_val == max(a_int.take(i as int)),
            1 <= i <= a_int.len()
    {
        let current = a_int[i];
        if current < min_val {
            min_val = current;
        }
        if current > max_val {
            max_val = current;
        }
        
        proof {
            lemma_min_prefix(a_int, (i + 1) as int);
            let prev = a_int.take(i as int);
            lemma_push_min(prev, current);
            lemma_push_max(prev, current);
            assert(a_int.take((i + 1) as int) == prev.push(current));
        }
        
        i += 1;
    }
    
    proof {
        lemma_min_max_nonempty(a_int);
        assert(min_val <= max_val);
    }
    
    (max_val - min_val) as i32
}
// </vc-code>

fn main() {}

}