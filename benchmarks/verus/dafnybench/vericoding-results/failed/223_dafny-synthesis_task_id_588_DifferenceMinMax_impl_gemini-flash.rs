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
#[verifier(nonlinear_arith)]
proof fn lemma_min_take_len_minus_1(s: Seq<int>, i: int)
    requires
        1 <= i <= s.len(),
    ensures
        min(s.take(i)) <= s[i - 1],
        forall |j: int| 0 <= j < i ==> min(s.take(i)) <= s[j],
{
    if i == 1 {
        assert(min(s.take(1)) == s[0]);
    } else {
        let prefix = s.take(i - 1);
        let min_prefix = min(prefix);
        if s[i - 1] <= min_prefix {
            assert(min(s.take(i)) == s[i - 1]);
        } else {
            assert(min(s.take(i)) == min_prefix);
            lemma_min_take_len_minus_1(s, i - 1);
        }
    }
}

proof fn lemma_max_take_len_minus_1(s: Seq<int>, i: int)
    requires
        1 <= i <= s.len(),
    ensures
        max(s.take(i)) >= s[i - 1],
        forall |j: int| 0 <= j < i ==> max(s.take(i)) >= s[j],
{
    if i == 1 {
        assert(max(s.take(1)) == s[0]);
    } else {
        let prefix = s.take(i - 1);
        let max_prefix = max(prefix);
        if s[i - 1] >= max_prefix {
            assert(max(s.take(i)) == s[i - 1]);
        } else {
            assert(max(s.take(i)) == max_prefix);
            lemma_max_take_len_minus_1(s, i - 1);
        }
    }
}

proof fn lemma_min_ext_equal(s: Seq<int>, v: int)
    requires
        0 < s.len(),
    ensures
        min(s.push(v)) == {
            if v < min(s) {
                v
            } else {
                min(s)
            }
        },
{
    if s.len() == 1 {
        if v < s[0] {
            assert(min(s.push(v)) == v);
        } else {
            assert(min(s.push(v)) == s[0]);
        }
    } else {
        let s_prime = s.take(s.len() - 1);
        let last_s = s[s.len() - 1];

        lemma_min_ext_equal(s_prime, last_s);

        let min_s_prime = min(s_prime);
        let min_s = if last_s <= min_s_prime { last_s } else { min_s_prime };

        if v <= min_s {
            assert(min(s.push(v)) == v);
        } else {
            assert(min(s.push(v)) == min_s);
        }
    }
}

proof fn lemma_max_ext_equal(s: Seq<int>, v: int)
    requires
        0 < s.len(),
    ensures
        max(s.push(v)) == {
            if v > max(s) {
                v
            } else {
                max(s)
            }
        },
{
    if s.len() == 1 {
        if v > s[0] {
            assert(max(s.push(v)) == v);
        } else {
            assert(max(s.push(v)) == s[0]);
        }
    } else {
        let s_prime = s.take(s.len() - 1);
        let last_s = s[s.len() - 1];

        lemma_max_ext_equal(s_prime, last_s);

        let max_s_prime = max(s_prime);
        let max_s = if last_s >= max_s_prime { last_s } else { max_s_prime };

        if v >= max_s {
            assert(max(s.push(v)) == v);
        } else {
            assert(max(s.push(v)) == max_s);
        }
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
    let mut min_val: i32 = a[0];
    let mut max_val: i32 = a[0];

    // a_seq needs to be ghost to correctly map `v as int`
    let ghost a_seq = a@.map(|k, v| v as int);

    if a.len() == 1 {
        assert(min(a_seq) == a_seq[0]);
        assert(max(a_seq) == a_seq[0]);
        return max_val - min_val;
    }

    let mut i: usize = 1;

    while i < a.len()
        invariant
            i <= a.len(),
            min_val == min(a_seq.take(i as int)), // min_val is the min of elements seen so far
            max_val == max(a_seq.take(i as int)), // max_val is the max of elements seen so far
            0 < i <= a.len(),
    {
        let current_val = a[i];

        proof {
            let s_prev = a_seq.take(i as int);
            let s_next = a_seq.take((i + 1) as int);
            let current_val_int = current_val as int;

            lemma_min_ext_equal(s_prev, current_val_int);
            lemma_max_ext_equal(s_prev, current_val_int);

            if current_val < min_val {
                assert(current_val_int < min_val as int);
                assert(min_val as int == min(s_prev));
                assert(min_val as int == min(s_prev) && current_val_int < min(s_prev));
                assert(min(s_next) == current_val_int);
            } else {
                assert(current_val_int >= min_val as int);
                assert(min_val as int == min(s_prev));
                assert(min(s_next) == min_val as int);
            }

            if current_val > max_val {
                assert(current_val_int > max_val as int);
                assert(max_val as int == max(s_prev));
                assert(max(s_next) == current_val_int);
            } else {
                assert(current_val_int <= max_val as int);
                assert(max_val as int == max(s_prev));
                assert(max(s_next) == max_val as int);
            }
        }

        if current_val < min_val {
            min_val = current_val;
        }

        if current_val > max_val {
            max_val = current_val;
        }

        i = i + 1;
    }

    max_val - min_val
}
// </vc-code>

fn main() {}

}