// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn correct_result(n: int, arr: Seq<int>, result: int) -> bool {
    &&& (sum_seq(arr) % n == 0 ==> result == n)
    &&& (sum_seq(arr) % n != 0 ==> result == n - 1)
    &&& (result == n || result == n - 1)
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_seq_empty()
    ensures sum_seq(Seq::<int>::empty()) == 0
{
}

proof fn sum_seq_single(x: int)
    ensures sum_seq(seq![x]) == x
{
    assert(seq![x].subrange(1, 1) =~= Seq::<int>::empty());
}

proof fn sum_seq_bounds(s: Seq<int>)
    requires s.len() > 0
    ensures sum_seq(s) == s[0] + sum_seq(s.subrange(1, s.len() as int))
{
}

fn compute_sum(arr: &Vec<i8>) -> (sum: i32)
    ensures sum == sum_seq(arr@.map(|i: int, x: i8| x as int))
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            total == sum_seq(arr@.map(|j: int, x: i8| x as int).subrange(0, i as int))
    {
        proof {
            let mapped = arr@.map(|j: int, x: i8| x as int);
            let prev_sub = mapped.subrange(0, i as int);
            let next_sub = mapped.subrange(0, (i + 1) as int);
            
            assert(next_sub =~= prev_sub.push(mapped[i as int]));
            assert(next_sub.len() == i + 1);
            assert(next_sub[i as int] == arr[i] as int);
            
            if i == 0 {
                assert(prev_sub =~= Seq::<int>::empty());
                sum_seq_empty();
                sum_seq_single(arr[0] as int);
            } else {
                assert(next_sub[0] == prev_sub[0]);
                assert(next_sub.subrange(1, next_sub.len() as int) =~= prev_sub.subrange(1, prev_sub.len() as int).push(arr[i] as int));
            }
        }
        
        total = total + (arr[i] as i32);
        i = i + 1;
    }
    
    proof {
        assert(arr@.map(|j: int, x: i8| x as int).subrange(0, arr.len() as int) =~= arr@.map(|j: int, x: i8| x as int));
    }
    
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    let sum = compute_sum(&arr);
    
    if sum % (n as i32) == 0 {
        proof {
            assert(sum_seq(arr@.map(|i: int, x: i8| x as int)) == sum);
            assert(sum % n == 0);
        }
        n
    } else {
        proof {
            assert(sum_seq(arr@.map(|i: int, x: i8| x as int)) == sum);
            assert(sum % n != 0);
        }
        n - 1
    }
}
// </vc-code>


}

fn main() {}