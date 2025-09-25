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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}