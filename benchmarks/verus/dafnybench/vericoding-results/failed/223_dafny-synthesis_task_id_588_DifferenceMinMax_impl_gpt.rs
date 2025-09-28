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
proof fn lemma_take_index<T>(s: Seq<T>, n: nat, k: nat)
    requires
        k < n,
        n <= s.len(),
    ensures
        s.take(n)[k] == s[k]
{
    assert(s.take(n)[k] == s[k]);
}

proof fn lemma_take_take_prefix<T>(s: Seq<T>, n: nat, m: nat)
    requires
        m <= n,
        n <= s.len(),
    ensures
        s.take(n).take(m) == s.take(m)
{
    assert(s.take(n).take(m) == s.take(m));
}

proof fn lemma_take_len<T>(s: Seq<T>, n: nat)
    requires
        n <= s.len(),
    ensures
        s.take(n).len() == n
{
    assert(s.take(n).len() == n);
}

proof fn lemma_take_full<T>(s: Seq<T>)
    ensures
        s.take(s.len()) == s
{
    assert(s.take(s.len()) == s);
}

proof fn lemma_min_take_succ(s: Seq<int>, n: nat)
    requires
        1 < n,
        n <= s.len(),
    ensures
        min(s.take(n)) == if s[n - 1] <= min(s.take(n - 1)) {
            s[n - 1]
        } else {
            min(s.take(n - 1))
        }
{
    let a = s.take(n);
    lemma_take_len::<int>(s, n);
    assert(a.len() == n);
    assert(a.len() > 1);
    assert(min(a) == {
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
    });
    lemma_take_take_prefix::<int>(s, n, n - 1);
    let prefix = a.take(a.len() - 1);
    assert(prefix == s.take(n - 1));
    lemma_take_index::<int>(s, n, n - 1);
    assert(a[a.len() - 1] == s[n - 1]);
    assert(min(a) == if s[n - 1] <= min(s.take(n - 1)) {
        s[n - 1]
    } else {
        min(s.take(n - 1))
    });
}

proof fn lemma_max_take_succ(s: Seq<int>, n: nat)
    requires
        1 < n,
        n <= s.len(),
    ensures
        max(s.take(n)) == if s[n - 1] >= max(s.take(n - 1)) {
            s[n - 1]
        } else {
            max(s.take(n - 1))
        }
{
    let a = s.take(n);
    lemma_take_len::<int>(s, n);
    assert(a.len() == n);
    assert(a.len() > 1);
    assert(max(a) == {
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
    });
    lemma_take_take_prefix::<int>(s, n, n - 1);
    let prefix = a.take(a.len() - 1);
    assert(prefix == s.take(n - 1));
    lemma_take_index::<int>(s, n, n - 1);
    assert(a[a.len() - 1] == s[n - 1]);
    assert(max(a) == if s[n - 1] >= max(s.take(n - 1)) {
        s[n - 1]
    } else {
        max(s.take(n - 1))
    });
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
    let mut i:
// </vc-code>

fn main() {}

}