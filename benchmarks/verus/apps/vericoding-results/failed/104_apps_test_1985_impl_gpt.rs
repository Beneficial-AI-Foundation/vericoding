// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn compute_initial_score(pos: int, a: Seq<int>, b: Seq<int>) -> int
    recommends 0 <= pos < a.len(), b.len() > 0
{
    b[0] - sum(a.subrange(0, pos + 1))
}

spec fn compute_backward_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
    decreases pos
    when pos >= 0
{
    if pos == 0 { 
        set![score_at_pos] 
    } else { 
        set![score_at_pos].union(compute_backward_scores(pos - 1, score_at_pos - a[pos], a))
    }
}

spec fn compute_forward_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
    decreases a.len() - pos
    when pos < a.len()
{
    if pos == a.len() - 1 { 
        Set::empty() 
    } else { 
        compute_forward_scores(pos + 1, score_at_pos + a[pos + 1], a).insert(score_at_pos + a[pos + 1])
    }
}

spec fn compute_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
{
    let backwards = compute_backward_scores(pos, score_at_pos, a);
    let forwards = compute_forward_scores(pos, score_at_pos, a);
    backwards.union(forwards)
}

spec fn is_valid_initial_score(pos: int, k: int, a: Seq<int>, b: Seq<int>) -> bool
    recommends 0 <= pos < k, k > 0, a.len() == k, b.len() > 0
{
    let scores = compute_scores(pos, b[0], a);
    forall|j: int| 0 <= j < b.len() ==> #[trigger] scores.contains(b[j])
}

spec fn valid_initial_scores(k: int, a: Seq<int>, b: Seq<int>) -> Set<int>
    recommends 
        k > 0,
        a.len() == k,
        b.len() > 0,
        forall|i: int| 0 <= i < k ==> -2000 <= #[trigger] a[i] <= 2000,
        forall|i: int| 0 <= i < b.len() ==> -4000000 <= #[trigger] b[i] <= 4000000
{
    Set::new(|x: int| exists|i: int| #[trigger] is_valid_initial_score(i, k, a, b) && 0 <= i < k && x == compute_initial_score(i, a, b))
}

spec fn valid_input(k: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
{
    k > 0 && n > 0 && a.len() == k && b.len() == n && n <= k &&
    (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] b[i] != #[trigger] b[j]) &&
    (forall|i: int| 0 <= i < k ==> -2000 <= #[trigger] a[i] <= 2000) &&
    (forall|i: int| 0 <= i < n ==> -4000000 <= #[trigger] b[i] <= 4000000)
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_subrange(a: Seq<int>, lo: int, hi_excl: int) -> int
    requires
        0 <= lo <= hi_excl <= a.len(),
    ensures
        sum_subrange == sum(a.subrange(lo, hi_excl)),
{
}

spec fn sum_range_inclusive(a: Seq<int>, lo: int, hi: int) -> int
    recommends 0 <= lo <= hi < a.len()
{
    sum(a.subrange(lo, hi + 1))
}

proof fn backward_membership_sound(pos: int, score: int, a: Seq<int>, t: int)
    requires
        0 <= pos < a.len(),
        1 <= t <= pos,
    ensures
        compute_backward_scores(pos, score, a).contains(score - sum_range_inclusive(a, t, pos)),
{
    if pos == 0 {
    } else {
        if t == pos {
        } else {
            backward_membership_sound(pos - 1, score - a[pos], a, t);
        }
    }
}

proof fn backward_membership_base_includes_score(pos: int, score: int, a: Seq<int>)
    requires
        0 <= pos < a.len(),
    ensures
        compute_backward_scores(pos, score, a).contains(score),
{
}

proof fn forward_membership_sound(pos: int, score: int, a: Seq<int>, u: int)
    requires
        0 <= pos < a.len(),
        pos + 1 <= u < a.len(),
    ensures
        compute_forward_scores(pos, score, a).contains(score + sum_range_inclusive(a, pos + 1, u)),
{
    if pos == a.len() - 1 {
    } else {
        if u == pos + 1 {
        } else {
            forward_membership_sound(pos + 1, score + a[pos + 1], a, u);
        }
    }
}

proof fn in_compute_scores_if_reachable(
    pos: int,
    score: int,
    a: Seq<int>,
    target: int,
    reached_by: int,
    is_backward: bool,
)
    requires
        0 <= pos < a.len(),
        (
            (!is_backward && pos + 1 <= reached_by && reached_by < a.len() && target == score + sum_range_inclusive(a, pos + 1, reached_by)) ||
            (is_backward && 1 <= reached_by && reached_by <= pos && target == score - sum_range_inclusive(a, reached_by, pos)) ||
            (is_backward && reached_by == 0 && target == score)
        ),
    ensures
        compute_scores(pos, score, a).contains(target),
{
    if is_backward {
        if reached_by == 0 {
            backward_membership_base_includes_score(pos, score, a);
        } else {
            backward_membership_sound(pos, score, a, reached_by);
        }
    } else {
        forward_membership_sound(pos, score, a, reached_by);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, n: i8, a: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires
        valid_input(k as int, n as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures
        result >= 0,
        result <= k,
        result as int == valid_initial_scores(k as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)).len(),
// </vc-spec>
// <vc-code>
{
    let k_usize: usize = k as usize;
    let n_usize: usize = n as usize;

    let a_len = a.len();
    let b_len = b.len();

    proof {
        assert(a_len as int == k as int);
        assert(b_len as int == n as int);
    }

    let mut valid_flags: Vec<bool> = Vec::new();
    let mut values: Vec<i64> = Vec::new();
    let mut prefix_sums: Vec<i64> = Vec::new();

    // Build prefix sums of a as i64 to avoid overflow
    let mut acc: i64 = 0;
    let mut i: usize = 0;
    while i < a_len
        invariant
            i <= a_len,
            prefix_sums.len() == i,
        decreases a_len - i
    {
        acc = acc + (a[i] as i64);
        prefix_sums.push(acc);
        i = i + 1;
    }

    // Helper to get sum a[0..=idx] as i64
    let get_prefix = |idx: usize| -> i64 {
        if idx < prefix_sums.len() { prefix_sums[idx] } else { 0 }
    };

    // score at position reference is b[0]
    let base_score: i64 = if b_len > 0 { b[0] as i64 } else { 0 };

    let mut pos: usize = 0;
    while pos < a_len
        invariant
            pos <= a_len,
            valid_flags.len() == pos,
            // values vector contains unique entries
            forall|x: int, y: int|
                0 <= x < values.len() as int && 0 <= y < values.len() as int && x != y ==> values[x as usize] != values[y as usize],
        decreases a_len - pos
    {
        // Check if this position is valid: all b[j] are reachable from base_score using a around pos
        let mut all_ok = true;
        let mut j: usize = 0;
        while j < b_len
            invariant
                j <= b_len,
                all_ok ==> (
                    forall|t: int|
                        0 <= t < j as int ==> {
                            let target = b[t as usize] as i64; true
                        }
                ),
            decreases b_len - j
        {
            let target = b[j] as i64;
            // Direct hit
            let mut ok = target == base_score;

            // Backward search: subtract a[pos] + a[pos-1] + ... + a[1]
            if !ok {
                let mut s: i64 = 0;
                let mut q: isize = pos as isize;
                while q >= 1
                    invariant
                        -1 <= q && q <= pos as isize,
                    decreases if q >= 1 { q as nat } else { 0 }
                {
                    s = s + (a[q as usize] as i64);
                    let cand = base_score - s;
                    if cand == target { ok = true; }
                    q = q - 1;
                }
            }

            // Forward search: add a[pos+1] + ...
            if !ok {
                let mut s2: i64 = 0;
                let mut r: usize = if pos + 1 < a_len { pos + 1 } else { a_len };
                while r < a_len
                    invariant
                        pos + 1 <= r <= a_len,
                    decreases a_len - r
                {
                    s2 = s2 + (a[r] as i64);
                    let cand2 = base_score + s2;
                    if cand2 == target { ok = true; }
                    r = r + 1;
                }
            }

            if !ok { all_ok = false; }
            j = j + 1;
        }

        valid_flags.push(all_ok);

        // If valid, compute initial score value and insert if new (dedupe by earlier values vector)
        if all_ok {
            let init_score = base_score - get_prefix(pos);
            let mut exists_before = false;
            let mut t: usize = 0;
            while t < values.len()
                invariant
                    t <= values.len(),
                decreases values.len() - t
            {
                if values[t] == init_score { exists_before = true; }
                t = t + 1;
            }
            if !exists_before {
                values.push(init_score);
            }
        }

        pos = pos + 1;
    }

    // Result is number of distinct initial scores collected
    let result_count: i8 = values.len() as i8;

    proof {
        assert(0 <= values.len() as int);
        assert(values.len() as int <= k as int);
    }

    result_count
}
// </vc-code>


}

fn main() {}