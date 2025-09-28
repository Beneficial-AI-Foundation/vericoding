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
    /* code modified by LLM (iteration 5): Fixed type errors by using executable types instead of ghost types */
    let ghost ratings_seq = ratings@.map(|i: int, x: i8| x as int);
    let ghost k_int = k as int;
    
    let mut count_k: usize = 0;
    let mut sum_ratings: i32 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            n as usize == ratings.len(),
            count_k as int == count_occurrences(ratings_seq.take(i as int), k_int),
            sum_ratings as int == sum(ratings_seq.take(i as int)),
        decreases n as usize - i
    {
        if ratings[i] == k {
            count_k = count_k + 1;
        }
        sum_ratings = sum_ratings + ratings[i] as i32;
        i = i + 1;
    }
    
    proof {
        assert(ratings_seq.take(n as int) =~= ratings_seq);
        assert(count_k as int == count_occurrences(ratings_seq, k_int));
        assert(sum_ratings as int == sum(ratings_seq));
    }
    
    if count_k == n as usize {
        // All players already have rating k
        proof {
            assert(ratings_seq.contains(k_int));
            assert(count_occurrences(ratings_seq, k_int) == ratings_seq.len());
        }
        0
    } else if count_k > 0 {
        // At least one player has rating k, can infect all in one contest
        proof {
            assert(ratings_seq.contains(k_int));
            assert(count_occurrences(ratings_seq, k_int) != ratings_seq.len());
        }
        1
    } else {
        // No player has rating k
        if sum_ratings == (k as i32) * (n as i32) {
            // Average is exactly k, can get all to k in one contest
            proof {
                assert(!ratings_seq.contains(k_int));
                assert(k_int * ratings_seq.len() == sum(ratings_seq));
            }
            1
        } else {
            // Need two contests
            proof {
                assert(!ratings_seq.contains(k_int));
                assert(k_int * ratings_seq.len() != sum(ratings_seq));
            }
            2
        }
    }
}
// </vc-code>


}

fn main() {}