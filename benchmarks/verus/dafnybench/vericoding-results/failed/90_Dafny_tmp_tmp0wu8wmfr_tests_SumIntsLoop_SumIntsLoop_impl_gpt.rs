use vstd::prelude::*;

verus! {

spec fn sum_ints(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else {
        sum_ints(n - 1) + n
    }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut s: u32 = 0;

    while i < n
        invariant
            i <= n,
            // relation to the recursive spec
            s == sum_ints(i as int),
            // closed form maintained at each step
            s == i * (i + 1) / 2,
        decreases (n - i) as int
    {
        let ip1 = i + 1;

        // update sum
        s = s + ip1;

        // update index
        i = ip1;

        proof {
            // Show the spec relation progresses:
            // sum_ints(i) after update equals sum_ints((i-1)+1) = sum_ints(i-1) + i
            // But we updated i already, so use the previous i (ip1 - 1) in reasoning
            // Let k be the previous i
            // Using arithmetic on ints for the recursive equation:
            assert(sum_ints((i as int)) == sum_ints((i as int) - 1) + (i as int));
        }

        // Maintain the closed-form invariant via algebra:
        // Previously: s_old = k*(k+1)/2
        // Now: s_new = s_old + (k+1) = (k*(k+1))/2 + (k+1) = ((k+1)*(k+2))/2
        // which matches i*(i+1)/2 with i = k+1.
        assert(s == i * (i + 1) / 2);
        assert(s == sum_ints(i as int));
    }

    s
}
// </vc-code>

fn main() {
}

}