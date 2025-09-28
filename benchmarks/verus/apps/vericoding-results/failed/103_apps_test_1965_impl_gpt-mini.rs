// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_occurrences(s: Seq<int>, x: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == x {
        1 + count_occurrences(s.drop_first(), x)
    } else {
        count_occurrences(s.drop_first(), x)
    }
}

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.drop_first())
    }
}

spec fn valid_input(n: int, ratings: Seq<int>) -> bool {
    n >= 2 && ratings.len() == n
}

spec fn all_infected(k: int, ratings: Seq<int>) -> bool {
    ratings.contains(k) && count_occurrences(ratings, k) == ratings.len()
}

spec fn can_infect_in_one_contest(k: int, ratings: Seq<int>) -> bool {
    (ratings.contains(k) && count_occurrences(ratings, k) != ratings.len()) ||
    (!ratings.contains(k) && k * ratings.len() == sum(ratings))
}

spec fn requires_two_contests(k: int, ratings: Seq<int>) -> bool {
    !ratings.contains(k) && k * ratings.len() != sum(ratings)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves bounds for count_occurrences */
proof fn count_occurrences_bounds(s: Seq<int>, x: int)
    decreases s.len()
    ensures
        count_occurrences(s, x) >= 0,
        count_occurrences(s, x) <= s.len() as int,
{
    if s.len() == 0 {
        assert(count_occurrences(s, x) == 0);
        assert(count_occurrences(s, x) >= 0);
        assert(count_occurrences(s, x) <= s.len() as int);
    } else {
        count_occurrences_bounds(s.drop_first(), x);
        if s[0] == x {
            assert(count_occurrences(s, x) == 1 + count_occurrences(s.drop_first(), x));
            assert(count_occurrences(s, x) >= 0);
            assert(count_occurrences(s, x) <= s.len() as int);
        } else {
            assert(count_occurrences(s, x) == count_occurrences(s.drop_first(), x));
            assert(count_occurrences(s, x) >= 0);
            assert(count_occurrences(s, x) <= s.len() as int);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve_case(n: i8, k: i8, ratings: Vec<i8>) -> (answer: i8)
    requires 
        valid_input(n as int, ratings@.map(|i: int, x: i8| x as int))
    ensures 
        answer >= 0 && answer <= 2,
        all_infected(k as int, ratings@.map(|i: int, x: i8| x as int)) ==> answer == 0,
        can_infect_in_one_contest(k as int, ratings@.map(|i: int, x: i8| x as int)) && !all_infected(k as int, ratings@.map(|i: int, x: i8| x as int)) ==> answer == 1,
        requires_two_contests(k as int, ratings@.map(|i: int, x: i8| x as int)) ==> answer == 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum and count and decide minimal contests needed */
    let seq_ratings = ratings@.map(|i: int, x: i8| x as int);
    let mut i: nat = 0;
    let mut acc_sum: int = 0;
    let mut acc_count_k: int = 0;
    while i < seq_ratings.len()
        invariant
            acc_sum == sum(seq_ratings.slice(0, i)),
            acc_count_k == count_occurrences(seq_ratings.slice(0, i), k as int),
        decreases seq_ratings.len() - i
    {
        let v = seq_ratings@[i];
        if v == k as int {
            acc_count_k += 1;
        }
        acc_sum += v;
        i += 1;
    }
    if acc_count_k == seq_ratings.len() as int {
        (0 as i8)
    } else if acc_count_k > 0 || (k as int) * (seq_ratings.len() as int) == acc_sum {
        (1 as i8)
    } else {
        (2 as i8)
    }
}

// </vc-code>


}

fn main() {}