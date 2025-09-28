// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_query(k: int, n: int, a: int, b: int) -> bool {
    k > 0 && n > 0 && a > 0 && b > 0 && b < a
}

spec fn max_action_a_turns(k: int, n: int, a: int, b: int) -> int {
    if n * b > k { 
        -1
    } else { 
        let max_possible = (k - n * b - 1) / (a - b);
        if n <= max_possible { n } else { max_possible }
    }
}

spec fn valid_result(result: int, k: int, n: int, a: int, b: int) -> bool {
    result == -1 || (0 <= result <= n)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_max_action_a_turns_range(result: int, k: int, n: int, a: int, b: int)
    requires
        k > 0,
        n > 0,
        a > 0,
        b > 0,
        b < a,
        result == max_action_a_turns(k, n, a, b),
    ensures
        valid_result(result, k, n, a, b),
{
    if n * b > k {
        assert(result == -1);
        assert(valid_result(-1, k, n, a, b));
    } else {
        let max_possible = (k - n * b - 1) / (a - b);
        assert(max_possible >= 0);
        let computed = if n <= max_possible { n } else { max_possible };
        assert(result == computed);
        assert(0 <= computed <= n);
        assert(valid_result(computed, k, n, a, b));
    }
}

proof fn lemma_max_action_a_turns_properties(k: int, n: int, a: int, b: int, x: int)
    requires
        k > 0,
        n > 0,
        a > 0,
        b > 0,
        b < a,
        n * b <= k,
        x == max_action_a_turns(k, n, a, b),
    ensures
        0 <= x <= n,
        x * a + (n - x) * b <= k,
        (x + 1) * a + (n - x - 1) * b > k || x == n,
{
    let max_possible = (k - n * b - 1) / (a - b);
    if n <= max_possible {
        assert(x == n);
        assert(x * a + (n - x) * b == n * b <= k);
        assert((x + 1) * a + (n - x - 1) * b > k || x == n);
    } else {
        assert(x == max_possible);
        assert(0 <= max_possible < n);
        
        // Prove x * a + (n - x) * b <= k
        let total = x * a + (n - x) * b;
        let divisor = a - b;
        let k_minus_nb = k - n * b;
        let remainder = (k_minus_nb - 1) % divisor;
        
        assert(k_minus_nb - 1 == x * divisor + remainder);
        assert(0 <= remainder < divisor);
        assert(k_minus_nb > x * divisor);
        assert(k_minus_nb > x * (a - b));
        assert(n * b + x * (a - b) < k);
        assert(total < k);
        
        // Prove (x + 1) * a + (n - x - 1) * b > k
        let next_total = (x + 1) * a + (n - x - 1) * b;
        assert(next_total == total + (a - b));
        assert(remainder >= 0);
        assert(total + remainder + 1 == k);
        assert(a - b > remainder + 1);
        assert(next_total > total + remainder + 1 == k);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<(i8, i8, i8, i8)>) -> (results: Vec<i8>)
    requires 
        queries.len() > 0,
        forall|i: int| 0 <= i < queries.len() ==> valid_query(#[trigger] queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
    ensures 
        results.len() == queries.len(),
        forall|i: int| 0 <= i < queries.len() ==> results[i as int] as int == max_action_a_turns(#[trigger] queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
        forall|i: int| 0 <= i < results.len() ==> valid_result(#[trigger] results[i as int] as int, queries[i as int].0 as int, queries[i as int].1 as int, queries[i as int].2 as int, queries[i as int].3 as int),
// </vc-spec>
// <vc-code>
{
    let mut results = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            i <= queries.len(),
            results.len() == i,
            forall|j: int| 0 <= j < i ==> results[j as int] as int == max_action_a_turns(#[trigger] queries[j as int].0 as int, queries[j as int].1 as int, queries[j as int].2 as int, queries[j as int].3 as int),
            forall|j: int| 0 <= j < i ==> valid_result(#[trigger] results[j as int] as int, queries[j as int].0 as int, queries[j as int].1 as int, queries[j as int].2 as int, queries[j as int].3 as int),
        decreases queries.len() - i
    {
        let (k, n, a, b) = queries[i];
        
        let k_val = k as int;
        let n_val = n as int;
        let a_val = a as int;
        let b_val = b as int;
        
        proof {
            assert(valid_query(k_val, n_val, a_val, b_val));
        }
        
        let result_val = max_action_a_turns(k_val, n_val, a_val, b_val);
        let result_i8 = if result_val == -1 {
            -1
        } else {
            if result_val <= 127 { result_val as i8 } else { 127i8 }
        };
        
        proof {
            lemma_max_action_a_turns_range(result_val, k_val, n_val, a_val, b_val);
        }
        
        results.push(result_i8);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}