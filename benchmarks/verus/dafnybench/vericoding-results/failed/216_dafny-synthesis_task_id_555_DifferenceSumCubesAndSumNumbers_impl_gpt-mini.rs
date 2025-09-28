use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_difference_identity_int(n: u32)
    ensures
        ((n as int) * (n as int) * (n as int + 1) * (n as int + 1) / 4
         - (n as int) * (n as int + 1) / 2)
        ==
        {
            let ni = n as int;
            let k = ni * (ni + 1);
            let m = k / 2;
            m * m - m
        }
{
    proof {
        let ni: int = n as int;
        let k: int = ni * (ni + 1);
        // k is product of two consecutive integers, so it is even
        if ni % 2 == 0 {
            assert(k % 2 == 0);
        } else {
            assert((ni + 1) % 2 == 0);
            assert(k % 2 == 0);
        }
        let half: int = k / 2;
        // (k*k)/4 == (k/2)*(k/2)
        assert((k * k) / 4 == half * half);
        assert(
            (ni * ni * (ni + 1) * (ni + 1)) / 4
            - (ni * (ni + 1)) / 2
            == half * half - half
        );
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    let nn: u128 = n as u128;
    let k: u128 = nn * (nn + 1u128);
    let m: u128 = k / 2u128; // n*(n+1)/2 computed in u128
    let diff128: u128 = m * m - m; // m*(m-1) in u128
    let diff: u32 = diff128 as u32;
    proof {
        // Use the integer lemma to relate the algebraic expression to m*m - m (in int)
        lemma_difference_identity_int(n);
        // Relate the u128 computed value to its int counterpart
        assert((diff128 as int) == (m as int) * (m as int) - (m as int));
        // By the lemma, that equals the algebraic RHS in int
        assert((m as int) * (m as int) - (m as int)
               == ( (n as int) * (n as int) * (n as int + 1) * (n as int + 1) / 4
                    - (n as int) * (n as int + 1) / 2 ));
        // Finally relate the spec RHS (computed in int then casted) to the returned u32
        assert((( (n as int) * (n as int) * (n as int + 1) * (n as int + 1) / 4
                  - (n as int) * (n as int + 1) / 2 ) as u32) == diff);
    }
    diff
}
// </vc-code>

fn main() {}

}