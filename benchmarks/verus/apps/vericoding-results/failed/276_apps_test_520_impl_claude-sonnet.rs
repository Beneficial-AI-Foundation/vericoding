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
proof fn sum_range_property(s: Seq<int>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures sum_range(s, start, end) == s.subrange(start, end).fold_left(0, |acc: int, x| acc + x)
    decreases end - start
{
    if start == end {
        assert(s.subrange(start, end).len() == 0);
        assert(s.subrange(start, end).fold_left(0, |acc: int, x| acc + x) == 0);
    } else {
        let sub_seq = s.subrange(start, end);
        let tail_seq = s.subrange(start + 1, end);
        assert(sub_seq[0] == s[start]);
        assert(sub_seq.drop_first() == tail_seq);
        sum_range_property(s, start + 1, end);
        assert(sum_range(s, start + 1, end) == tail_seq.fold_left(0, |acc: int, x| acc + x));
    }
}

proof fn sum_range_extensional(s1: Seq<int>, s2: Seq<int>, start: int, end: int)
    requires 0 <= start <= end <= s1.len() && s1.len() == s2.len(),
        forall|i: int| start <= i < end ==> s1[i] == s2[i]
    ensures sum_range(s1, start, end) == sum_range(s2, start, end)
    decreases end - start
{
    if start < end {
        sum_range_extensional(s1, s2, start + 1, end);
    }
}

proof fn sum_range_increment(s: Seq<int>, start: int, i: int)
    requires 0 <= start <= i < s.len()
    ensures sum_range(s, start, i + 1) == sum_range(s, start, i) + s[i]
    decreases i - start
{
    if start == i {
        assert(sum_range(s, start, i) == 0);
        assert(sum_range(s, start, i + 1) == s[i]);
    } else {
        sum_range_increment(s, start + 1, i);
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
    /* code modified by LLM (iteration 5): fixed type error in proof block */
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    
    while i < years.len()
        invariant
            0 <= i <= years.len(),
            sum == sum_range(years@.map(|j, x| x as int), 0, i as int),
            sum <= (i as i64) * 127
        decreases years.len() - i
    {
        proof {
            let mapped_seq = years@.map(|j, x| x as int);
            sum_range_increment(mapped_seq, 0, i as int);
            assert(sum_range(mapped_seq, 0, (i + 1) as int) == sum_range(mapped_seq, 0, i as int) + mapped_seq[i as int]);
            assert(mapped_seq[i as int] == years@[i as int] as int);
        }
        sum = sum + years[i] as i64;
        i = i + 1;
    }
    
    proof {
        let mapped_seq = years@.map(|j, x| x as int);
        assert(sum == sum_range(mapped_seq, 0, years.len() as int));
    }
    
    let avg = sum / (n as i64);
    #[verifier::truncate]
    avg as i8
}
// </vc-code>


}

fn main() {}