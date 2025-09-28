// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n > 0 && k > 0
}

spec fn is_strictly_increasing(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i+1]
}

spec fn all_positive(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn valid_sequence(s: Seq<int>, n: int, k: int) -> bool
{
    s.len() == k && all_positive(s) && is_strictly_increasing(s) && sum_seq(s) == n
}

spec fn is_possible(n: int, k: int) -> bool
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic bounds for solution */
proof fn solution_bounds(n: int, k: int)
    requires
        valid_input(n, k),
        is_possible(n, k),
    ensures
        k >= 1,
        n - k*(k+1)/2 >= 0,
        k + (n - k*(k+1)/2) <= n,
    decreases
        k,
{
    proof {
        assert(k > 0);
        assert(k*(k+1)/2 <= n);
        assert(n - k*(k+1)/2 >= 0);
        assert(k + (n - k*(k+1)/2) <= n);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, k as int)
    ensures 
        ((result.len() == 1 && result[0] == -1) || 
         (valid_sequence(result@.map(|_i: int, x: i8| x as int), n as int, k as int))) &&
        ((result.len() == 1 && result[0] == -1) <==> !is_possible(n as int, k as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct increasing sequence 1..k-1 and adjust last element without using 'int' in executable code */
    let min_sum = (k as i64) * ((k as i64) + 1) / 2;
    if min_sum > (n as i64) {
        let mut res: Vec<i8> = Vec::new();
        res.push(-1);
        res
    } else {
        let r = (n as i64) - min_sum;
        let mut res: Vec<i8> = Vec::new();
        let mut i: i32 = 1;
        while i < k as i32
            invariant
                1 <= i as int,
                i as int <= k as int,
                res.len() as int == i as int - 1,
                forall|j: int| 0 <= j < res.len() as int ==> res@[j] as int == j + 1,
            decreases
                (k as int) - i as int,
        {
            res.push(i as i8);
            i += 1;
        }
        res.push((k as i64 + r) as i8);
        proof {
            // Prove the postconditions in spec using spec-level integers
            let n_int = n as int;
            let k_int = k as int;
            assert(k_int > 0);
            assert(k_int * (k_int + 1) / 2 <= n_int);
            // length: after loop res.len() == k-1, after push it is k
            assert(res.len() as int == k_int);
            // first k-1 elements are 1..k-1 (from loop invariant)
            assert(forall|j: int| 0 <= j < (k_int - 1) ==> res@[j] as int == j + 1);
            // last element equals k + (n - k*(k+1)/2)
            assert(res@[k_int - 1] as int == k_int + (n_int - k_int*(k_int+1)/2));
            // strictly increasing
            assert(forall|j: int| 0 <= j < res.len() as int - 1 ==> res@[j] as int < res@[j+1] as int);
            // all positive
            assert(forall|j: int| 0 <= j < res.len() as int ==> res@[j] as int > 0);
            // sum: sum of first k-1 is (k-1)*k/2, plus last element equals n
            assert(sum_seq(res@.map(|_i: int, x: i8| x as int)) ==
                   (k_int * (k_int - 1) / 2) + (k_int + (n_int - k_int*(k_int+1)/2)));
            assert(sum_seq(res@.map(|_i: int, x: i8| x as int)) == n_int);
        }
        res
    }
}

// </vc-code>


}

fn main() {}