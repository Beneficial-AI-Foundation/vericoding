// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    decreases n when n > 0
{
    if n > 0 && n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    decreases a.len() - i when 0 <= i <= a.len()
{
    if 0 <= i < a.len() && (forall|j: int| 0 <= j < a.len() ==> a[j] > 0) {
        count_factors_of_two(a[i]) + sum_factors(a, i + 1)
    } else if i == a.len() {
        0
    } else {
        0
    }
}

spec fn max_operations(a: Seq<int>) -> int {
    if valid_input(a) { sum_factors(a, 0) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added unfolding lemma and executable helpers; moved spec asserts into proof blocks to avoid parsing issues */
proof fn lemma_sum_unfold(a: Seq<int>, i: int)
    requires
        valid_input(a),
        0 <= i < a.len(),
    ensures
        sum_factors(a, i) == count_factors_of_two(a[i]) + sum_factors(a, i + 1),
{
    proof {
        assert(valid_input(a));
        assert(0 <= i < a.len());
        assert(sum_factors(a, i) == count_factors_of_two(a[i]) + sum_factors(a, i + 1));
    }
}

/* helper modified by LLM (iteration 2): executable counter for factors of two with suitable invariants */
fn count_twos_exec(n: int) -> (res: int)
    requires
        n > 0,
    ensures
        res == count_factors_of_two(n),
        res >= 0,
{
    let mut k: int = n;
    let mut c: int = 0;
    while k > 0 && k % 2 == 0
        invariant
            k > 0,
            c >= 0,
            c + count_factors_of_two(k) == count_factors_of_two(n),
        decreases k
    {
        k = k / 2;
        c = c + 1;
    }
    c
}

/* helper modified by LLM (iteration 2): compute sum of factors with a verified loop tying to the spec */
fn compute_sum(a: &Vec<i8>) -> (res: int)
    requires
        valid_input(a@.map(|i, x| x as int)),
    ensures
        res == max_operations(a@.map(|i, x| x as int)),
        res >= 0,
{
    let s = a@.map(|i, x| x as int);
    let mut total: int = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            s.len() == a.len() as int,
            valid_input(s),
            total >= 0,
            total + sum_factors(s, i as int) == sum_factors(s, 0),
        decreases a.len() as int - i as int
    {
        let xi_int: int = a[i] as int;
        proof {
            assert(0 <= i as int && i as int < s.len());
            assert(valid_input(s));
            assert(s[i as int] > 0);
        }
        let c_i = count_twos_exec(xi_int);
        proof {
            // relate xi_int and s[i]
            assert(0 <= i as int && i as int < s.len());
            assert(s[i as int] == (a@[i as int]) as int);
            assert(a@[i as int] == a[i]);
            assert(xi_int == s[i as int]);
            // unfold sum at position i
            lemma_sum_unfold(s, i as int);
            assert(sum_factors(s, i as int) == count_factors_of_two(s[i as int]) + sum_factors(s, i as int + 1));
            assert(c_i == count_factors_of_two(xi_int));
            assert(c_i == count_factors_of_two(s[i as int]));
            assert(total + c_i + sum_factors(s, i as int + 1) == sum_factors(s, 0));
        }
        total = total + c_i;
        i = i + 1;
    }
    proof {
        assert(max_operations(s) == sum_factors(s, 0));
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result >= 0,
        result as int == max_operations(a@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute the specification result via helpers and return as i8 */
    let total: int = compute_sum(&a);
    let result_i8: i8 = total as i8;
    result_i8
}
// </vc-code>


}

fn main() {}