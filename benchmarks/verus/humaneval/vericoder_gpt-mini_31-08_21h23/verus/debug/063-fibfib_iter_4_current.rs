use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
proof fn spec_trib_recurrence(k: nat)
    ensures
        spec_fibfib(k + 3) == spec_fibfib(k + 2) + spec_fibfib(k + 1) + spec_fibfib(k)
{
    // Reveal the definition so we can use the recursion directly
    reveal(spec_fibfib);
    // k + 3 >= 3 for any nat k, so spec_fibfib matches the recursive branch
    assert(k + 3 >= 3);
    // By the definition of spec_fibfib for inputs >= 3:
    // spec_fibfib(k+3) == spec_fibfib(k+2) + spec_fibfib(k+1) + spec_fibfib(k))
    assert(spec_fibfib(k + 3) == spec_fibfib(k + 2) + spec_fibfib(k + 1) + spec_fibfib(k));
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: nat = x as nat;
    if n == 0 {
        Some(0u32)
    } else if n == 1 {
        Some(0u32)
    } else if n == 2 {
        Some(1u32)
    } else {
        // runtime values held in sufficiently-large unsigned integers to detect overflow
        let mut a: u128 = 0u128; // F(i-3)
        let mut b: u128 = 0u128; // F(i-2)
        let mut c: u128 = 1u128; // F(i-1)
        // runtime loop index
        let mut i_r: u32 = 3u32;
        // ghost (spec) counterparts (declare mutable ghost vars in one ghost block)
        ghost {
            let mut ga: nat = 0; // spec_fibfib(i-3)
            let mut gb: nat = 0; // spec_fibfib(i-2)
            let mut gc: nat = 1; // spec_fibfib(i-1)
            let mut i: nat = 3;
        }

        // Loop: iterate i = 3 ..= n, maintaining that (ga,gb,gc) are the spec values
        while i_r <= (n as u32)
            invariant
                3 <= i && i <= n + 1 &&
                i == i_r as nat &&
                a == ga as u128 &&
                b == gb as u128 &&
                c == gc as u128 &&
                ga == spec_fibfib(i - 3) &&
                gb == spec_fibfib(i - 2) &&
                gc == spec_fibfib(i - 1) &&
                a <= (u32::MAX as u128) &&
                b <= (u32::MAX as u128) &&
                c <= (u32::MAX as u128)
            decreases (n + 1) - i
        {
            // Compute next = F(i) = ga + gb + gc (spec) and as runtime u128
            let next: u128 = a + b + c;
            ghost let gnext: nat = ga + gb + gc;

            // relate runtime sum to ghost sum
            assert(next == (gnext as u128));

            // use spec lemma: spec_fibfib(i) == spec_fibfib(i-1)+spec_fibfib(i-2)+spec_fibfib(i-3)
            proof {
                // gnext == spec_fibfib(i) by spec_trib_recurrence with k = i - 3
                spec_trib_recurrence(i - 3);
                assert(gnext == spec_fibfib(i));
            }

            // If overflow would occur for u32, return None
            if next > (u32::MAX as u128) {
                return None;
            }

            // shift the window: (a,b,c) <- (b,c,next)
            a = b;
            b = c;
            c = next;

            // update runtime and ghost counterparts accordingly
            i_r = i_r + 1u32;
            ghost {
                ga = gb;
                gb = gc;
                gc = gnext;
                i = i + 1;
            }
        }

        // After loop, i == n + 1 and gc == spec_fibfib(n), and c == gc as u128
        proof {
            // from invariant: i == i_r and i_r == n + 1
            assert(i_r == n as u32 + 1u32);
            assert(i == i_r as nat);
            assert(i == n + 1);
            assert(gc == spec_fibfib(n));
            assert(c == gc as u128);
            assert(c <= (u32::MAX as u128));
        }

        Some((c as u32))
    }
    // impl-end
}
// </vc-code>

fn main() {}
}