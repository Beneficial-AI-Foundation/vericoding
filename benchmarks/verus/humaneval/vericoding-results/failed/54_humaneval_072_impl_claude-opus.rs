// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_palindrome(s: Seq<int>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> s[i] == s[s.len() - 1 - i]
}

spec fn sum_elements(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_elements(s.subrange(1, s.len() as int))
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to properly handle recursive case */
proof fn lemma_sum_append(s: Seq<int>, x: int)
    ensures sum_elements(s.push(x)) == sum_elements(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(sum_elements(seq![x]) == x);
    } else {
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x).subrange(1, s.push(x).len() as int) =~= s.subrange(1, s.len() as int).push(x));
        lemma_sum_append(s.subrange(1, s.len() as int), x);
        assert(sum_elements(s.push(x)) == s.push(x)[0] + sum_elements(s.push(x).subrange(1, s.push(x).len() as int)));
        assert(sum_elements(s.push(x)) == s[0] + sum_elements(s.subrange(1, s.len() as int).push(x)));
        assert(sum_elements(s.push(x)) == s[0] + sum_elements(s.subrange(1, s.len() as int)) + x);
        assert(sum_elements(s) == s[0] + sum_elements(s.subrange(1, s.len() as int)));
        assert(sum_elements(s.push(x)) == sum_elements(s) + x);
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(q: Vec<i8>, w: i8) -> (result: bool)
    ensures result == (is_palindrome(q@.map(|i: int, x: i8| x as int)) && sum_elements(q@.map(|i: int, x: i8| x as int)) <= w as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed incorrect overflow assertions and simplified sum computation */
    let n = q.len();
    let mut is_pal = true;
    let mut i: usize = 0;
    
    // Check palindrome
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            is_pal == (forall|j: int| #![trigger q@[j]] 0 <= j < i ==> q@[j] == q@[n as int - 1 - j]),
            n == q.len(),
        decreases n / 2 - i
    {
        if q[i] != q[n - 1 - i] {
            is_pal = false;
        }
        i = i + 1;
    }
    
    // Compute sum
    let mut sum: i64 = 0;
    let mut j: usize = 0;
    
    while j < n
        invariant
            0 <= j <= n,
            n == q.len(),
            sum == sum_elements(q@.subrange(0, j as int).map(|k: int, x: i8| x as int)),
        decreases n - j
    {
        let elem_val = q[j] as i64;
        sum = sum + elem_val;
        
        proof {
            let prev_seq = q@.subrange(0, j as int).map(|k: int, x: i8| x as int);
            let next_seq = q@.subrange(0, (j + 1) as int).map(|k: int, x: i8| x as int);
            
            assert(next_seq =~= prev_seq.push(q@[j as int] as int));
            lemma_sum_append(prev_seq, q@[j as int] as int);
            assert(sum_elements(next_seq) == sum_elements(prev_seq) + q@[j as int] as int);
        }
        
        j = j + 1;
    }
    
    proof {
        assert(q@.subrange(0, n as int) =~= q@);
        assert(q@.subrange(0, n as int).map(|k: int, x: i8| x as int) =~= q@.map(|k: int, x: i8| x as int));
    }
    
    is_pal && sum <= w as i64
}
// </vc-code>


}

fn main() {}