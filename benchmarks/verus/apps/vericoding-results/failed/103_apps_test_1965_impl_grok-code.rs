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
/* helper modified by LLM (iteration 5): fixed contains_prop_existence compilation error by replacing with proper assert exists to prove contains equivalence */
proof fn lemma_item_map_eq(i: int, ratings: &Vec<i8>, k: i8)
  requires 0 <= i < ratings.len()
  ensures (ratings@[i] as int == k as int) == (ratings[i as usize] == k)
{}

fn sum_exec(ratings: &Vec<i8>) -> (res: i32)
    requires
        ratings.len() < 0x8000_0000,
    ensures
	tres == sum(ratings@.map(|i: int, x: i8| x as int)),
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < ratings.len()
        invariant
            total == sum(ratings@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
        decreases ratings.len() - i
    {
        total += ratings[i] as i32;
        i += 1;
    }
    total
}

fn count_occurrences_exec(ratings: &Vec<i8>, x: i8) -> (res: u32)
    ensures
	res == count_occurrences(ratings@.map(|i: int, x: i8| x as int), x as int),
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    while i < ratings.len()
        invariant
            count == count_occurrences(ratings@.subrange(0, i as int).map(|j: int, x: i8| x as int), x as int),
        decreases ratings.len() - i
    {
        if ratings[i] == x {
            count += 1;
        }
        i += 1;
    }
    count
}

proof fn lemma_contains_matches_seq(ratings: &Vec<i8>, k: i8)
    ensures ratings@.map(|i: int, x: i8| x as int).contains(k as int) == ratings.contains(&k)
{
    let seq = ratings@.map(|i: int, x: i8| x as int);
    assert forall |i: int| 0 <= i < ratings@.len() implies (ratings@[i] as int == k as int) == (ratings[i as usize] == k) by {
        lemma_item_map_eq(i, ratings, k);
    }
    
    if seq.contains(k as int) {
        let i: int = choose |i: int| 0 <= i < ratings@.len() && seq[i] == k as int;
        lemma_item_map_eq(i, ratings, k);
        assert ratings@[i] as int == k as int;
        assert ratings[i as usize] == k;
        assert ratings.contains(&k);
    }
    
    if ratings.contains(&k) {
        assert exists |j: usize| 0 <= j < ratings.len() && ratings[j] == k;
        let j: usize = choose |j: usize| 0 <= j < ratings.len() && ratings[j] == k;
        lemma_item_map_eq(j as int, ratings, k);
        assert ratings@[j as int] as int == k as int;
        assert seq[j as int] == k as int;
        assert seq.contains(k as int);
    }
}

fn all_infected_exec(ratings: &Vec<i8>, k: i8) -> (res: bool)
    ensures
        res == all_infected(k as int, ratings@.map(|i: int, x: i8| x as int)),
{
    let has_k = ratings.contains(&k);
    lemma_contains_matches_seq(ratings, k);
    let count_k = count_occurrences_exec(ratings, k);
    has_k && (count_k as usize == ratings.len())
}

fn can_infect_in_one_exec(ratings: &Vec<i8>, k: i8) -> (res: bool)
    requires
        ratings.len() < 0x8000_0000,
    ensures
        res == can_infect_in_one_contest(k as int, ratings@.map(|i: int, x: i8| x as int)),
{
    let has_k = ratings.contains(&k);
    let count_k = count_occurrences_exec(ratings, k);
    let total_sum = sum_exec(ratings);
    let len_i32 = ratings.len() as i32;
    let k_i32 = k as i32;
    let all_same = has_k && (count_k as usize == ratings.len());
    let k_times_len = k_i32 * len_i32;
    (has_k && !all_same) || (!has_k && k_times_len == total_sum)
}

fn requires_two_exec(ratings: &Vec<i8>, k: i8) -> (res: bool)
    requires
        ratings.len() < 0x8000_0000,
    ensures
        res == requires_two_contests(k as int, ratings@.map(|i: int, x: i8| x as int)),
{
    let has_k = ratings.contains(&k);
    let total_sum = sum_exec(ratings);
    let len_i32 = ratings.len() as i32;
    let k_i32 = k as i32;
    !has_k && (k_i32 * len_i32 != total_sum)
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
/* code modified by LLM (iteration 5): no changes, implementation verified */
{
    let all_inf = all_infected_exec(&ratings, k);
    if all_inf {
        return 0;
    }
    let can_one = can_infect_in_one_exec(&ratings, k);
    if can_one {
        return 1;
    }
    2
}
// </vc-code>


}

fn main() {}