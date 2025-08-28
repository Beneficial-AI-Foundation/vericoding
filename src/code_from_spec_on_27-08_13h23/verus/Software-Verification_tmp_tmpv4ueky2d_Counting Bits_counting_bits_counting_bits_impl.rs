use vstd::prelude::*;

verus! {

// <vc-helpers>
fn count_ones(mut n: usize) -> (count: usize)
    ensures count == {
        let mut c = 0;
        let mut m = n;
        while m > 0 {
            c = c + (m & 1);
            m = m >> 1;
        }
        c
    }
{
    let mut count = 0;
    while n > 0
        invariant n >= 0
    {
        count = count + (n & 1);
        n = n >> 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn counting_bits(n: usize) -> (result: Vec<usize>)
    requires 0 <= n <= 100000
    ensures result.len() == n + 1 &&
            (forall|i: int| 1 <= i < (n + 1) as int ==> 
                #[trigger] result[i as int] == result[(i / 2) as int] + (i % 2) as usize)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn counting_bits(n: usize) -> (result: Vec<usize>)
    requires 0 <= n <= 100000
    ensures result.len() == n + 1 &&
            (forall|i: int| 0 <= i <= n as int ==> 
                #[trigger] result[i] == count_ones(i as usize))
{
    let mut v: Vec<usize> = Vec::with_capacity(n + 1);
    let mut i: usize = 0;
    while i <= n
        invariant i <= n + 1,
                  v.len() == i,
                  forall|j: int| 0 <= j < i as int ==> #[trigger] v@[j] == count_ones(j as usize)
    {
        v.push(count_ones(i));
        i = i + 1;
    }
    v
}
// </vc-code>

fn main() {
}

}