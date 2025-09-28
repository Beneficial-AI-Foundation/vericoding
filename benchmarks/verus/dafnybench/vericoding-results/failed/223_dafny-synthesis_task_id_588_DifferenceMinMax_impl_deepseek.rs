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
proof fn lemma_min_take_append(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        a.len() > 0,
    ensures
        min(a.take(i + 1)) == if a[i] <= min(a.take(i)) { a[i] } else { min(a.take(i)) },
    decreases i
{
    if i == 0 {
        assert(a.take(1) === seq![a[0]]);
        assert(min(a.take(1)) == a[0]);
        assert(a.take(0) === Seq::empty());
    } else {
        lemma_min_take_append(a, i - 1);
        let s_prefix = a.take(i);
        let s = a.take(i + 1);
        if a[i] <= min(s_prefix) {
            assert(min(s) == a[i]);
        } else {
            assert(min(s) == min(s_prefix));
        }
    }
}

proof fn lemma_max_take_append(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        a.len() > 0,
    ensures
        max(a.take(i + 1)) == if a[i] >= max(a.take(i)) { a[i] } else { max(a.take(i)) },
    decreases i
{
    if i == 0 {
        assert(a.take(1) === seq![a[0]]);
        assert(max(a.take(1)) == a[0]);
        assert(a.take(0) === Seq::empty());
    } else {
        lemma_max_take_append(a, i - 1);
        let s_prefix = a.take(i);
        let s = a.take(i + 1);
        if a[i] >= max(s_prefix) {
            assert(max(s) == a[i]);
        } else {
            assert(max(s) == max(s_prefix));
        }
    }
}

spec fn min_elt(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i
{
    if i == 0 {
        a[0]
    } else {
        let prev = min_elt(a, i - 1);
        if a[i] <= prev {
            a[i]
        } else {
            prev
        }
    }
}

spec fn max_elt(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i
{
    if i == 0 {
        a[0]
    } else {
        let prev = max_elt(a, i - 1);
        if a[i] >= prev {
            a[i]
        } else {
            prev
        }
    }
}

proof fn lemma_min_equals(a: Seq<int>)
    requires a.len() > 0,
    ensures min(a) == min_elt(a, a.len() as int - 1),
    decreases a.len(),
{
    if a.len() == 1 {
        assert(min(a) == a[0]);
        assert(min_elt(a, 0) == a[0]);
    } else {
        let prefix = a.take(a.len() - 1);
        lemma_min_equals(prefix);
        assert(min(a) == if a[a.len() - 1] <= min(prefix) {a[a.len() - 1]} else {min(prefix)});
        assert(min_elt(a, a.len() as int - 1) == if a[a.len() - 1] <= min_elt(prefix, prefix.len() as int - 1) {a[a.len() - 1]} else {min_elt(prefix, prefix.len() as int - 1)});
        assert(min(prefix) == min_elt(prefix, prefix.len() as int - 1));
    }
}

proof fn lemma_max_equals(a: Seq<int>)
    requires a.len() > 0,
    ensures max(a) == max_elt(a, a.len() as int - 1),
    decreases a.len(),
{
    if a.len() == 1 {
        assert(max(a) == a[0]);
        assert(max_elt(a, 0) == a[0]);
    } else {
        let prefix = a.take(a.len() - 1);
        lemma_max_equals(prefix);
        assert(max(a) == if a[a.len() - 1] >= max(prefix) {a[a.len() - 1]} else {max(prefix)});
        assert(max_elt(a, a.len() as int - 1) == if a[a.len() - 1] >= max_elt(prefix, prefix.len() as int - 1) {a[a.len() - 1]} else {max_elt(prefix, prefix.len() as int - 1)});
        assert(max(prefix) == max_elt(prefix, prefix.len() as int - 1));
    }
}

proof fn lemma_min_monotonic(a: Seq<int>, i: int, j: int)
    requires
        a.len() > 0,
        0 <= i <= j < a.len(),
    ensures
        min_elt(a, j) <= min_elt(a, i),
    decreases j - i,
{
    if i < j {
        lemma_min_monotonic(a, i, j - 1);
        let prev = min_elt(a, j - 1);
        if a[j] <= prev {
            assert(min_elt(a, j) == a[j]);
            assert(a[j] <= prev);
            assert(prev <= min_elt(a, i));
        } else {
            assert(min_elt(a, j) == prev);
        }
    }
}

proof fn lemma_max_monotonic(a: Seq<int>, i: int, j: int)
    requires
        a.len() > 0,
        0 <= i <= j < a.len(),
    ensures
        max_elt(a, i) <= max_elt(a, j),
    decreases j - i,
{
    if i < j {
        lemma_max_monotonic(a, i, j - 1);
        let prev = max_elt(a, j - 1);
        if a[j] >= prev {
            assert(max_elt(a, j) == a[j]);
            assert(a[j] >= prev);
            assert(prev >= max_elt(a, i));
        } else {
            assert(max_elt(a, j) == prev);
        }
    }
}

proof fn lemma_min_elt_base(a: Seq<int>)
    requires a.len() > 0,
    ensures min_elt(a, 0) == a[0]
{
}

proof fn lemma_max_elt_base(a: Seq<int>)
    requires a.len() > 0,
    ensures max_elt(a, 0) == a[0]
{
}

proof fn lemma_min_elt_step(a: Seq<int>, i: int)
    requires
        0 < i < a.len(),
    ensures
        min_elt(a, i) == if a[i] <= min_elt(a, i - 1) { a[i] } else { min_elt(a, i - 1) }
{
}

proof fn lemma_max_elt_step(a: Seq<int>, i: int)
    requires
        0 < i < a.len(),
    ensures
        max_elt(a, i) == if a[i] >= max_elt(a, i - 1) { a[i] } else { max_elt(a, i - 1) }
{
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut current_min = a[0];
    let mut current_max = a[0];
    let mut idx: usize = 1;
    
    proof {
        let s = a@.map(|i, x| x as int);
        lemma_min_elt_base(s);
        lemma_max_elt_base(s);
        assert(min_elt(s, 0) == s[0]);
        assert(max_elt(s, 0) == s[0]);
    }
    
    while idx < n
        invariant
            idx <= n,
            1 <= idx || idx == 0,
            current_min as int == min_elt(a@.map(|i, x| x as int), idx as int - 1),
            current_max as int == max_elt(a@.map(|i, x| x as int), idx as int - 1),
            min_elt(a@.map(|i, x| x as int), n as int - 1) <= current_min as int,
            current_max as int <= max_elt(a@.map(|i, x| x as int), n as int - 1),
        decreases n - idx,
    {
        let x = a[idx];
        proof {
            let s = a@.map(|i, x| x as int);
            lemma_min_monotonic(s, idx as int - 1, n as int - 1);
            lemma_max_monotonic(s, idx as int - 1, n as int - 1);
        }
        if x < current_min {
            current_min = x;
        }
        if x > current_max {
            current_max = x;
        }
        proof {
            let s = a@.map(|i, x| x as int);
            let current_idx = idx as int;
            lemma_min_elt_step(s, current_idx);
            lemma_max_elt_step(s, current_idx);
            
            assert(current_min as int == if (x as int) <= min_elt(s, current_idx - 1) {x as int} else {min_elt(s, current_idx - 1)});
            assert(current_min as int == min_elt(s, current_idx));
            
            assert(current_max as int == if (x as int) >= max_elt(s, current_idx - 1) {x as int} else {max_elt(s, current_idx - 1)});
            assert(current_max as int == max_elt(s, current_idx));
        }
        idx = idx + 1;
    }
    proof {
        let s = a@.map(|i, x| x as int);
        lemma_min_equals(s);
        lemma_max_equals(s);
        assert(min(s) == min_elt(s, s.len() as int - 1));
        assert(max(s) == max_elt(s, s.len() as int - 1));
        assert(min(s) == current_min as int);
        assert(max(s) == current_max as int);
    }
    current_max - current_min
}
// </vc-code>

fn main() {}

}