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
/* helper modified by LLM (iteration 5): Fixed native integer operations */
proof fn lemma_count_occurrences_contains(s: Seq<int>, x: int)
    requires
        s.contains(x),
    ensures
        count_occurrences(s, x) >= 1,
        count_occurrences(s, x) == s.len() <==> forall|i: int| 0 <= i < s.len() ==> s[i] == x
{
    if s.len() == 0 {
    } else {
        if s[0] == x {
            lemma_count_occurrences_contains(s.drop_first(), x);
        } else {
            lemma_count_occurrences_contains(s.drop_first(), x);
        }
    }
}

proof fn lemma_sum_avg_equals_k(s: Seq<int>, k: int)
    requires
        s.len() > 0,
    ensures
        k * s.len() == sum(s) <==> forall|i: int| 0 <= i < s.len() ==> s[i] == k
{
    if s.len() == 1 {
        assert(s[0] == k ==> k * s.len() == sum(s));
        assert(s[0] != k ==> k * s.len() != sum(s));
    } else {
        let rest = s.drop_first();
        if rest.len() > 0 {
            lemma_sum_avg_equals_k(rest, k);
        }
        if s[0] == k && (forall|i: int| 0 <= i < rest.len() ==> rest[i] == k) {
            assert(k * s.len() == sum(s));
            assert(forall|i: int| 0 <= i < s.len() ==> s[i] == k);
        } else {
            assert(k * s.len() != sum(s) || !forall|i: int| 0 <= i < s.len() ==> s[i] == k);
        }
    }
}

proof fn lemma_determine_case(k: int, ratings: Seq<int>)
    ensures
        if all_infected(k, ratings) {
            0
        } else if can_infect_in_one_contest(k, ratings) {
            1
        } else {
            2
        } >= 0,
        all_infected(k, ratings) ==> 0 >= 0 && 0 <= 2,
        can_infect_in_one_contest(k, ratings) && !all_infected(k, ratings) ==> 1 >= 0 && 1 <= 2,
        requires_two_contests(k, ratings) ==> 2 >= 0 && 2 <= 2
{
    reveal(all_infected);
    reveal(can_infect_in_one_contest);
    reveal(requires_two_contests);
    
    if ratings.contains(k) {
        lemma_count_occurrences_contains(ratings, k);
        if count_occurrences(ratings, k) == ratings.len() {
            assert(all_infected(k, ratings));
        } else {
            assert(can_infect_in_one_contest(k, ratings));
        }
    } else {
        if k * ratings.len() == sum(ratings) {
            lemma_sum_avg_equals_k(ratings, k);
            assert(can_infect_in_one_contest(k, ratings));
        } else {
            assert(requires_two_contests(k, ratings));
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
/* code modified by LLM (iteration 5): Fixed native integer operations and loop invariants */
{
    proof {
        lemma_determine_case(k as int, ratings@.map(|i: int, x: i8| x as int));
    }
    
    let mut total_rating: i32 = 0;
    let mut has_k = false;
    let mut count_k: u32 = 0;
    
    let mut i: usize = 0;
    while i < ratings.len()
        invariant
            0 <= i <= ratings.len(),
            total_rating == sum(ratings@.subrange(0, i as nat)) as i32,
            count_k == count_occurrences(ratings@.subrange(0, i as nat), k as int) as u32,
            has_k == count_k > 0
    {
        let r = ratings[i];
        total_rating += r as i32;
        if r == k {
            has_k = true;
            count_k += 1;
        }
        i += 1;
    }
    
    let n_int = n as i32;
    
    if count_k as usize == ratings.len() {
        0
    } else if has_k {
        1
    } else if (k as i32) * n_int == total_rating {
        1
    } else {
        2
    }
}
// </vc-code>


}

fn main() {}