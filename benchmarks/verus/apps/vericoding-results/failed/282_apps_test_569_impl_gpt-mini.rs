// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec function counting distinct elements in prefix */
spec fn count_prefix_distinct(s: Seq<char>, i: int) -> int
    requires
        0 <= i && i <= s.len(),
    decreases
        i,
{
    if i == 0 {
        0
    } else {
        let prev = count_prefix_distinct(s, i - 1);
        let is_new = forall |j: int| 0 <= j && j < i - 1 ==> s@[j] != s@[i - 1];
        prev + (if is_new { 1 } else { 0 })
    }
}

/* helper modified by LLM (iteration 4): spec function producing set of elements in prefix */
spec fn prefix_set(s: Seq<char>, i: int) -> Set<char>
    requires
        0 <= i && i <= s.len(),
    decreases
        i,
{
    if i == 0 {
        Set::empty()
    } else {
        prefix_set(s, i - 1).insert(s@[i - 1])
    }
}

/* helper modified by LLM (iteration 4): relate prefix count to prefix set length by induction */
proof fn count_prefix_equals_set_len(s: Seq<char>, i: int)
    requires
        0 <= i && i <= s.len(),
    ensures
        count_prefix_distinct(s, i) == prefix_set(s, i).len() as int,
    decreases
        i,
{
    if i == 0 {
        assert(count_prefix_distinct(s, 0) == 0);
        assert(prefix_set(s, 0).len() as int == 0);
    } else {
        count_prefix_equals_set_len(s, i - 1);
        let prev_count: int = count_prefix_distinct(s, i - 1);
        let prev_len: int = prefix_set(s, i - 1).len() as int;
        assert(prev_count == prev_len);
        if forall |j: int| 0 <= j && j < i - 1 ==> s@[j] != s@[i - 1] {
            // new element at position i-1
            assert(prefix_set(s, i).len() as int == prev_len + 1);
            assert(count_prefix_distinct(s, i) == prev_count + 1);
        } else {
            // element already present
            assert(prefix_set(s, i).len() as int == prev_len);
            assert(count_prefix_distinct(s, i) == prev_count);
        }
    }
}

/* helper modified by LLM (iteration 4): characterize membership of prefix_set by existence of index */
proof fn prefix_set_membership(s: Seq<char>, i: int, x: char)
    requires
        0 <= i && i <= s.len(),
    ensures
        prefix_set(s, i).contains(x) == (exists |k: int| 0 <= k && k < i && s@[k] == x),
    decreases
        i,
{
    if i == 0 {
        assert(!prefix_set(s, 0).contains(x));
    } else {
        prefix_set_membership(s, i - 1, x);
        assert(prefix_set(s, i).contains(x) == (prefix_set(s, i - 1).contains(x) || x == s@[i - 1]));
        assert(prefix_set(s, i - 1).contains(x) == (exists |k: int| 0 <= k && k < i - 1 && s@[k] == x));
        assert((exists |k: int| 0 <= k && k < i - 1 && s@[k] == x) || x == s@[i - 1] == (exists |k: int| 0 <= k && k < i && s@[k] == x));
    }
}

/* helper modified by LLM (iteration 4): show prefix_set for full length equals sequence to_set */
proof fn prefix_set_eq_to_set_full(s: Seq<char>)
    ensures
        prefix_set(s, s.len() as int) == s.to_set(),
{
    let n = s.len() as int;
    // show membership equivalence for every element
    assert(forall |x: char| prefix_set(s, n).contains(x) == (exists |k: int| 0 <= k && k < n && s@[k] == x));
    assert(forall |x: char| s.to_set().contains(x) == (exists |k: int| 0 <= k && k < n && s@[k] == x));
    assert(forall |x: char| prefix_set(s, n).contains(x) == s.to_set().contains(x));
    assert(prefix_set(s, n) == s.to_set());
}

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): compute distinct count using nested loops and maintain invariant using count_prefix_distinct */
    if n > 26 {
        -1
    } else {
        let mut distinct: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                distinct as int == count_prefix_distinct(s@, i as int),
            decreases n - i
        {
            let mut j: usize = 0;
            let mut seen: bool = false;
            while j < i
                invariant
                    j <= i,
                    (seen ==> exists |k: int| 0 <= k && k < j as int && s@[k] == s@[i as int]),
                    (!seen ==> forall |k: int| 0 <= k && k < j as int ==> s@[k] != s@[i as int]),
                decreases i - j
            {
                if s[j] == s[i] {
                    seen = true;
                }
                j += 1;
            }
            if !seen {
                distinct = distinct + 1;
            }
            i += 1;
        }
        let res = (n as i32) - (distinct as i32);
        proof {
            // relate runtime distinct to specification count and then to count_distinct_chars
            count_prefix_equals_set_len(s@, n as int);
            prefix_set_eq_to_set_full(s@);
            assert(distinct as int == count_prefix_distinct(s@, n as int));
            assert(count_prefix_distinct(s@, n as int) == prefix_set(s@, n as int).len() as int);
            assert(prefix_set(s@, n as int) == s@.to_set());
            assert(prefix_set(s@, n as int).len() as int == s@.to_set().len() as int);
            assert(distinct as int == s@.to_set().len() as int);
            assert(distinct as int == count_distinct_chars(s@));
        }
        res
    }
}

// </vc-code>


}

fn main() {}