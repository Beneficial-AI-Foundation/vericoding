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
proof fn sum_seq_push(s: Seq<int>, x: int)
    ensures
        sum_seq(s.push(x)) == sum_seq(s) + x,
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
    } else {
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s.subrange(1, s.len() as int).push(x));
        sum_seq_push(s.subrange(1, s.len() as int), x);
    }
}

proof fn sum_first_k(k: int)
    requires
        k >= 0,
    ensures
        sum_seq(Seq::new(k as nat, |i: int| i + 1)) == k * (k + 1) / 2,
    decreases k
{
    if k == 0 {
        assert(Seq::new(0, |i: int| i + 1) =~= Seq::empty());
    } else {
        let s = Seq::new(k as nat, |i: int| i + 1);
        let s_prev = Seq::new((k - 1) as nat, |i: int| i + 1);
        assert(s =~= s_prev.push(k));
        sum_first_k(k - 1);
        sum_seq_push(s_prev, k);
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
    /* code modified by LLM (iteration 2): Fixed int type usage in executable code */
    let min_sum_i8 = k * (k + 1) / 2;
    
    if n < min_sum_i8 {
        let mut result = Vec::new();
        result.push(-1i8);
        return result;
    }
    
    let mut result: Vec<i8> = Vec::new();
    let mut remaining = n;
    let mut i: usize = 0;
    
    while i < k as usize
        invariant
            i <= k,
            result.len() == i,
            remaining >= 0,
            remaining as int == n as int - sum_seq(result@.map(|_j: int, x: i8| x as int)),
            all_positive(result@.map(|_j: int, x: i8| x as int)),
            is_strictly_increasing(result@.map(|_j: int, x: i8| x as int)),
            i > 0 ==> result[i - 1] >= i as i8,
            remaining as int >= (k as int - i as int) * (k as int - i as int + 1) / 2,
        decreases k as usize - i
    {
        let positions_left = (k as i8 - i as i8 - 1);
        let min_for_rest = positions_left * (positions_left + 1) / 2;
        
        let min_val = if i == 0 { 1i8 } else { (result[i - 1] + 1) };
        let max_possible = remaining - min_for_rest;
        let val = if max_possible > min_val { max_possible } else { min_val };
        
        result.push(val);
        remaining = remaining - val;
        
        proof {
            sum_seq_push(result@.subrange(0, i as int).map(|_j: int, x: i8| x as int), val as int);
            assert(result@.subrange(0, (i + 1) as int) =~= result@);
        }
        
        i = i + 1;
    }
    
    proof {
        sum_first_k(k as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}