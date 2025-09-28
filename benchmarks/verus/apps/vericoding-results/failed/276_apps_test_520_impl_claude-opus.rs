// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_range(s: Seq<int>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start == end {
        0
    } else {
        s[start] + sum_range(s, start + 1, end)
    }
}

spec fn valid_input(n: int, years: Seq<int>) -> bool
{
    n > 0 && years.len() == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed bound logic and added proper helpers for sum properties */
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

proof fn sum_lemma(s: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= s.len()
    ensures
        sum_range(s, start, end) == if start == end { 0 } else { s[start] + sum_range(s, start + 1, end) }
    decreases end - start
{
}

proof fn sum_range_bounds(s: Seq<int>, start: int, end: int, bound: int)
    requires
        0 <= start <= end <= s.len(),
        bound >= 0,
        forall|i: int| start <= i < end ==> abs(s[i]) <= bound
    ensures
        abs(sum_range(s, start, end)) <= (end - start) * bound
    decreases end - start
{
    if start == end {
        assert(sum_range(s, start, end) == 0);
        assert(abs(0) == 0);
        assert(0 <= (end - start) * bound) by {
            assert(end - start == 0);
            assert((end - start) * bound == 0);
        }
    } else {
        assert(sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end));
        assert(abs(s[start]) <= bound);
        sum_range_bounds(s, start + 1, end, bound);
        assert(abs(sum_range(s, start + 1, end)) <= (end - start - 1) * bound);
        assert(abs(s[start] + sum_range(s, start + 1, end)) <= abs(s[start]) + abs(sum_range(s, start + 1, end)));
        assert(abs(s[start]) + abs(sum_range(s, start + 1, end)) <= bound + (end - start - 1) * bound);
        assert(bound + (end - start - 1) * bound == (end - start) * bound) by {
            assert(bound + (end - start - 1) * bound == bound * (1 + (end - start - 1)));
            assert(1 + (end - start - 1) == end - start);
        }
    }
}

proof fn sum_range_append(s: Seq<int>, start: int, end: int)
    requires
        0 <= start < end <= s.len()
    ensures
        sum_range(s, start, end) == sum_range(s, start, end - 1) + s[end - 1]
    decreases end - start
{
    if start == end - 1 {
        assert(sum_range(s, start, end - 1) == 0);
        assert(sum_range(s, start, end) == s[start]);
    } else {
        assert(sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end));
        sum_range_append(s, start + 1, end);
        assert(sum_range(s, start + 1, end) == sum_range(s, start + 1, end - 1) + s[end - 1]);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and bounds checking */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    assert(forall|j: int| 0 <= j < years.len() ==> -128 <= years[j as int] <= 127);
    
    while i < years.len()
        invariant
            i <= years.len(),
            sum as int == sum_range(years@.map(|j: int, x| x as int), 0, i as int),
            years.len() == n as nat,
            n <= 127,
            abs(sum as int) <= 128 * (i as int),
            forall|j: int| 0 <= j < i ==> -128 <= years[j as int] <= 127
        decreases years.len() - i
    {
        proof {
            assert(i < years.len());
            assert(-128 <= years[i as int] <= 127);
            
            let mapped_seq = years@.map(|j: int, x| x as int);
            assert(forall|j: int| 0 <= j < i ==> abs(mapped_seq[j]) <= 128);
            
            sum_range_bounds(mapped_seq, 0, i as int, 128);
            assert(abs(sum as int) <= 128 * (i as int));
            
            assert(mapped_seq.take(i as int) =~= years@.take(i as int).map(|j: int, x| x as int));
            assert(sum as int == sum_range(mapped_seq, 0, i as int));
            
            assert(-128 * (i as int) - 128 <= sum as int + years[i as int] as int);
            assert(sum as int + years[i as int] as int <= 128 * (i as int) + 127);
            assert(abs(sum as int + years[i as int] as int) <= 128 * (i + 1));
            
            let next_mapped = years@.take((i + 1) as int).map(|j: int, x| x as int);
            assert(next_mapped.take(i as int) =~= mapped_seq.take(i as int));
            sum_range_append(next_mapped, 0, (i + 1) as int);
            assert(sum_range(next_mapped, 0, (i + 1) as int) == sum_range(next_mapped, 0, i as int) + next_mapped[i as int]);
            assert(next_mapped[i as int] == years[i as int] as int);
        }
        
        sum = sum + years[i] as i32;
        
        proof {
            let next_mapped = years@.take((i + 1) as int).map(|j: int, x| x as int);
            assert(sum as int == sum_range(next_mapped, 0, (i + 1) as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == years.len());
        assert(years.len() == n as nat);
        assert(years@.take(n as int) =~= years@);
        let mapped = years@.map(|j: int, x| x as int);
        assert(sum as int == sum_range(mapped, 0, n as int));
        assert(sum as int == sum_range(years@.map(|j, x| x as int), 0, years.len() as int));
    }
    
    let avg = (sum / (n as i32)) as i8;
    avg
}
// </vc-code>


}

fn main() {}