// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
  n >= m > 0
}

spec fn sum(s: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 
    0int 
  } else { 
    s[0] + sum(s.subrange(1, s.len() as int)) 
  }
}

spec fn count(s: Seq<int>, val: int) -> int
  decreases s.len()
{
  if s.len() == 0 { 
    0int 
  } else { 
    (if s[0] == val { 1int } else { 0int }) + count(s.subrange(1, s.len() as int), val) 
  }
}

spec fn optimal_distribution(result: Seq<int>, n: int, m: int) -> bool {
  &&& m > 0
  &&& result.len() == m
  &&& (forall|i: int| 0 <= i < result.len() ==> result[i] > 0)
  &&& sum(result) == n
  &&& (forall|i: int| 0 <= i < result.len() ==> result[i] == n / m || result[i] == n / m + 1)
  &&& count(result, n / m) == m - (n % m)
  &&& count(result, n / m + 1) == n % m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed recursive proofs and added base case handling */
proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(sum(s.push(x)) == x);
        assert(sum(s) == 0);
    } else {
        let first = s[0];
        let rest = s.subrange(1, s.len() as int);
        assert(s.push(x) =~= seq![first].add(rest.push(x)));
        assert(sum(s.push(x)) == first + sum(rest.push(x)));
        lemma_sum_push(rest, x);
        assert(sum(rest.push(x)) == sum(rest) + x);
        assert(sum(s) == first + sum(rest));
        assert(sum(s.push(x)) == first + sum(rest) + x == sum(s) + x);
    }
}

proof fn lemma_count_push(s: Seq<int>, x: int, val: int)
    ensures count(s.push(x), val) == count(s, val) + if x == val { 1int } else { 0int }
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(count(s.push(x), val) == if x == val { 1int } else { 0int });
        assert(count(s, val) == 0);
    } else {
        let first = s[0];
        let rest = s.subrange(1, s.len() as int);
        assert(s.push(x) =~= seq![first].add(rest.push(x)));
        let first_count = if first == val { 1int } else { 0int };
        assert(count(s.push(x), val) == first_count + count(rest.push(x), val));
        lemma_count_push(rest, x, val);
        assert(count(rest.push(x), val) == count(rest, val) + if x == val { 1int } else { 0int });
        assert(count(s, val) == first_count + count(rest, val));
        assert(count(s.push(x), val) == count(s, val) + if x == val { 1int } else { 0int });
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost variable usage for sequence mapping */
    let mut result = Vec::new();
    let q = n / m;
    let r = n % m;
    let mut i: usize = 0;
    
    assert(q >= 0 && r >= 0 && r < m) by {
        assert(n >= m > 0);
        assert(q == n / m);
        assert(r == n % m);
    };
    
    assert(q < 127) by {
        assert(n < 128 && m > 0);
        assert(q == n / m);
        assert(q <= n);
    };
    
    while i < m as usize
        invariant
            0 <= i <= m,
            result.len() == i,
            sum(result@.map(|j: int, x: i8| x as int)) == if i <= r as usize { i as int * (q as int + 1) } else { r as int * (q as int + 1) + (i as int - r as int) * q as int },
            forall|j: int| 0 <= j < i ==> result@[j] as int == if j < r as int { q as int + 1 } else { q as int },
            count(result@.map(|j: int, x: i8| x as int), q as int) == if i <= r as usize { 0 } else { i as int - r as int },
            count(result@.map(|j: int, x: i8| x as int), q as int + 1) == if i <= r as usize { i as int } else { r as int },
            m > 0,
            q == n / m,
            r == n % m,
            q >= 0,
            q < 127,
        decreases m as usize - i
    {
        let val: i8 = if i < r as usize { (q + 1) as i8 } else { q };
        
        ghost let old_seq = result@.map(|j: int, x: i8| x as int);
        result.push(val);
        ghost let new_seq = result@.map(|j: int, x: i8| x as int);
        
        proof {
            assert(new_seq =~= old_seq.push(val as int));
            lemma_sum_push(old_seq, val as int);
            lemma_count_push(old_seq, val as int, q as int);
            lemma_count_push(old_seq, val as int, q as int + 1);
            
            if i < r as usize {
                assert(val as int == q as int + 1);
                assert(sum(new_seq) == sum(old_seq) + (q as int + 1));
                assert(count(new_seq, q as int) == count(old_seq, q as int));
                assert(count(new_seq, q as int + 1) == count(old_seq, q as int + 1) + 1);
            } else {
                assert(val as int == q as int);
                assert(sum(new_seq) == sum(old_seq) + q as int);
                assert(count(new_seq, q as int) == count(old_seq, q as int) + 1);
                assert(count(new_seq, q as int + 1) == count(old_seq, q as int + 1));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == m);
        assert(r as int * (q as int + 1) + (m as int - r as int) * q as int == n as int) by {
            assert(r as int * (q as int + 1) + (m as int - r as int) * q as int
                == r as int * q as int + r as int + m as int * q as int - r as int * q as int
                == m as int * q as int + r as int);
            assert(n as int == m as int * (n / m) + (n % m));
            assert(q as int == n / m);
            assert(r as int == n % m);
        };
        assert(sum(result@.map(|i: int, x: i8| x as int)) == n as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}