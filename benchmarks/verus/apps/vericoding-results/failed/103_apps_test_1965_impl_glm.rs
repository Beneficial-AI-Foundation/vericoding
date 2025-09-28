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
/* helper modified by LLM (iteration 4): added helper lemma to prove count_occurrences properties */
lemma count_occurrences_lemma(s: Seq<int>, x: int, i: int)
    requires 0 <= i <= s.len()
    ensures count_occurrences(s.take(i), x) == count_occurrences(s@[0..i], x)
{
    if i == 0 {
        assert(s.take(0) == Seq::empty());
        assert(s@[0..0] == Seq::empty());
    } else {
        count_occurrences_lemma(s.drop_first(), x, i - 1);
        if s[0] == x {
            assert(count_occurrences(s.take(i), x) == 1 + count_occurrences(s.drop_first().take(i - 1), x));
        } else {
            assert(count_occurrences(s.take(i), x) == count_occurrences(s.drop_first().take(i - 1), x));
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
/* code modified by LLM (iteration 4): fixed invariant syntax and added proper sequence mapping */
{
    let mut count = 0i8;
    let mut total = 0i32;
    let mut i = 0usize;

    while i < n as usize
        invariant
            0 <= i <= n as int,
            count_occurrences(ratings@.map(|x: i8| x as int).subrange(0, i as int), k as int) == count as int,
            sum(ratings@.map(|x: i8| x as int).subrange(0, i as int)) == total as int,
        decreases (n as int) - i
    {
        let rating_val = ratings[i];
        if rating_val == k {
            count += 1;
        }
        total += rating_val as i32;
        i += 1;
    }

    if count == n {
        0
    } else if count > 0 {
        1
    } else {
        if (k as i32) * (n as i32) == total {
            1
        } else {
            2
        }
    }
}
// </vc-code>


}

fn main() {}