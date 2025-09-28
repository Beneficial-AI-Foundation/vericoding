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
/* helper modified by LLM (iteration 5): added overflow bounds and better invariants */
proof fn count_occurrences_bounds(s: Seq<int>, x: int)
    ensures count_occurrences(s, x) >= 0,
            count_occurrences(s, x) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else if s[0] == x {
        count_occurrences_bounds(s.drop_first(), x);
    } else {
        count_occurrences_bounds(s.drop_first(), x);
    }
}

proof fn sum_bounds_helper(s: Seq<int>)
    requires s.len() > 0
    ensures sum(s) >= s[0] + sum(s.drop_first())
    decreases s.len()
{
}

fn count_k_in_vec(ratings: &Vec<i8>, k: i8) -> (count: usize)
    requires ratings.len() <= usize::MAX
    ensures count as int == count_occurrences(ratings@.map(|i: int, x: i8| x as int), k as int),
            count <= ratings.len()
{
    let mut count = 0usize;
    let mut i = 0usize;
    
    while i < ratings.len()
        invariant
            i <= ratings.len(),
            count <= i,
            count as int == count_occurrences(ratings@.take(i as int).map(|j: int, x: i8| x as int), k as int)
        decreases ratings.len() - i
    {
        if ratings[i] == k {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

fn compute_sum(ratings: &Vec<i8>) -> (total: i64)
    requires ratings.len() <= 1000000
    ensures total as int == sum(ratings@.map(|i: int, x: i8| x as int))
{
    let mut total = 0i64;
    let mut i = 0usize;
    
    while i < ratings.len()
        invariant
            i <= ratings.len(),
            total as int == sum(ratings@.take(i as int).map(|j: int, x: i8| x as int)),
            total >= 0,
            total <= i64::MAX / 2
        decreases ratings.len() - i
    {
        total = total + ratings[i] as i64;
        i = i + 1;
    }
    
    total
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
    /* code modified by LLM (iteration 5): fixed postcondition logic and overflow bounds */
    
    let count_k = count_k_in_vec(&ratings, k);
    
    // Case 1: All infected (k appears in all positions)
    if count_k == ratings.len() {
        return 0;
    }
    
    // Case 2: Can infect in one contest (k appears but not everywhere)
    if count_k > 0 {
        return 1;
    }
    
    // Case 3: k doesn't appear, check if sum equals expected
    let total_sum = compute_sum(&ratings);
    let expected_sum = (k as i64) * (ratings.len() as i64);
    
    if total_sum == expected_sum {
        1
    } else {
        2
    }
}
// </vc-code>


}

fn main() {}