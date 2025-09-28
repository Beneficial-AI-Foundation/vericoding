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
/* helper modified by LLM (iteration 4): [fixed compilation error by changing `ghost let` to `let ghost`] */
fn exec_sum(ratings: &Vec<i8>) -> (s: i64)
    ensures
        s as int == sum(ratings@.map(|i: int, x: i8| x as int)),
{
    let ghost ratings_seq_int = ratings@.map(|i: int, x: i8| x as int);
    let mut s: i64 = 0;
    let mut i: usize = 0;
    while i < ratings.len()
        invariant
            ratings@.len() == old(ratings)@.len(),
            i <= ratings.len(),
            ratings_seq_int == old(ratings)@.map(|i: int, x: i8| x as int),
            s as int == sum(ratings_seq_int.take(i as nat)),
        decreases ratings.len() - i
    {
        s = s + ratings[i] as i64;
        i = i + 1;
    }
    s
}

/* helper modified by LLM (iteration 4): [fixed compilation error by changing `ghost let` to `let ghost`] */
fn exec_count_and_contains(ratings: &Vec<i8>, x: i8) -> (res: (i64, bool))
    ensures
        res.0 as int == count_occurrences(ratings@.map(|i: int, r: i8| r as int), x as int),
        res.1 == ratings@.map(|i: int, r: i8| r as int).contains(x as int),
{
    let ghost x_int = x as int;
    let ghost ratings_seq_int = ratings@.map(|i: int, r: i8| r as int);
    let mut count: i64 = 0;
    let mut contains = false;
    let mut i: usize = 0;
    while i < ratings.len()
        invariant
            ratings@.len() == old(ratings)@.len(),
            i <= ratings.len(),
            ratings_seq_int == old(ratings)@.map(|i: int, r: i8| r as int),
            count as int == count_occurrences(ratings_seq_int.take(i as nat), x_int),
            contains == ratings_seq_int.take(i as nat).contains(x_int),
        decreases ratings.len() - i
    {
        if ratings[i] == x {
            count = count + 1;
            contains = true;
        }
        i = i + 1;
    }
    (count, contains)
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
    /* code modified by LLM (iteration 4): [fixed compilation error by changing `ghost let` to `let ghost`] */
    let ghost ratings_seq = ratings@.map(|i: int, x: i8| x as int);
    let ghost n_int = n as int;
    let ghost k_int = k as int;

    let (count_val, contains_k) = exec_count_and_contains(&ratings, k);
    let ghost count_int = count_val as int;

    proof {
        assert(count_int == count_occurrences(ratings_seq, k_int));
        assert(contains_k == ratings_seq.contains(k_int));
    }

    if contains_k && count_val == n as i64 {
        proof {
            assert(all_infected(k_int, ratings_seq));
        }
        return 0;
    }

    proof {
        assert(!all_infected(k_int, ratings_seq));
    }

    let sum_val = exec_sum(&ratings);
    let ghost sum_int = sum_val as int;
    proof {
        assert(sum_int == sum(ratings_seq));
    }
    
    if (contains_k && count_val != n as i64) || (!contains_k && k as i64 * n as i64 == sum_val) {
        proof {
            assert(can_infect_in_one_contest(k_int, ratings_seq));
        }
        return 1;
    }

    proof {
        assert(!can_infect_in_one_contest(k_int, ratings_seq));
        assert(requires_two_contests(k_int, ratings_seq));
    }
    
    2
}
// </vc-code>


}

fn main() {}