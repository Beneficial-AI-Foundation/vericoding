// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn valid_input(n: int, d: int, t: Seq<int>) -> bool {
    1 <= n <= 100 && 1 <= d <= 10000 &&
    t.len() == n &&
    forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] >= 1 && #[trigger] t[i] <= 100
}

spec fn min_time_needed(n: int, t: Seq<int>) -> int {
    sum_seq(t) + 10 * (n - 1)
}

spec fn valid_result(n: int, d: int, t: Seq<int>, result: int) -> bool {
    let song_sum = sum_seq(t);
    let min_time = min_time_needed(n, t);
    if min_time > d {
        result == -1
    } else {
        result == (d - song_sum) / 5 && result >= 0
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_seq_bounds(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 1 && s[i] <= 100,
        s.len() >= 0,
    ensures
        sum_seq(s) >= s.len(),
        sum_seq(s) <= 100 * s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sum_seq_bounds(s.subrange(1, s.len() as int));
    }
}

proof fn sum_seq_single(x: int)
    ensures sum_seq(seq![x]) == x
{
    assert(seq![x].subrange(1, 1) =~= Seq::<int>::empty());
}

proof fn sum_seq_append(s: Seq<int>, x: int)
    ensures sum_seq(s.push(x)) == sum_seq(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        sum_seq_single(x);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        sum_seq_append(s_tail, x);
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s_tail.push(x));
    }
}

fn compute_sum(t: &Vec<i8>) -> (sum: i32)
    requires
        t@.len() >= 1,
        t@.len() <= 100,
        forall|i: int| 0 <= i < t@.len() ==> t@[i] >= 1 && t@[i] <= 100,
    ensures
        sum == sum_seq(t@.map(|_i: int, x: i8| x as int)),
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    let ghost mut processed = Seq::<int>::empty();
    
    while i < t.len()
        invariant
            0 <= i <= t.len(),
            processed.len() == i,
            sum == sum_seq(processed),
            forall|j: int| 0 <= j < i ==> processed[j] == t@[j] as int,
            t@.len() >= 1,
            t@.len() <= 100,
            forall|j: int| 0 <= j < t@.len() ==> t@[j] >= 1 && t@[j] <= 100,
        decreases t.len() - i
    {
        let val = t[i] as i32;
        sum = sum + val;
        proof {
            processed = processed.push(t@[i as int] as int);
            sum_seq_append(processed.subrange(0, i as int), t@[i as int] as int);
            assert(processed.subrange(0, i as int) =~= processed.take(i as int));
        }
        i = i + 1;
    }
    
    proof {
        assert(t@.map(|_i: int, x: i8| x as int).len() == t@.len());
        assert(forall|j: int| 0 <= j < t@.len() ==> t@.map(|_i: int, x: i8| x as int)[j] == t@[j] as int);
        assert(processed =~= t@.map(|_i: int, x: i8| x as int));
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, t: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, t@.map(|_i: int, x: i8| x as int))
    ensures valid_result(n as int, d as int, t@.map(|_i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed ghost variable declaration */
    let ghost t_int = t@.map(|_i: int, x: i8| x as int);
    proof {
        sum_seq_bounds(t_int);
    }
    
    let song_sum = compute_sum(&t);
    let min_time = song_sum + 10 * ((n - 1) as i32);
    
    if min_time > d as i32 {
        return -1;
    } else {
        let result = ((d as i32) - song_sum) / 5;
        proof {
            assert(min_time == min_time_needed(n as int, t_int));
            assert(result == ((d as int) - sum_seq(t_int)) / 5);
            assert(result >= 0);
        }
        result as i8
    }
}
// </vc-code>


}

fn main() {}