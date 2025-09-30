// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_test_case(a: nat, b: nat, n: nat, m: nat) -> bool
{
    n + m > 0
}

spec fn can_satisfy_all_guests(a: nat, b: nat, n: nat, m: nat) -> bool
{
    a + b >= n + m &&
    m <= min(a, b)
}

spec fn min(x: nat, y: nat) -> nat
{
    if x <= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma for min equivalence */
proof fn lemma_min_equiv(x: nat, y: nat)
    ensures
        min(x, y) == if x <= y { x } else { y },
{
    if x <= y {
        assert(min(x, y) == x);
    } else {
        assert(min(x, y) == y);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve_cookie_distribution(a: u8, b: u8, n: u8, m: u8) -> (result: bool)
    requires
        valid_test_case(a as nat, b as nat, n as nat, m as nat),
    ensures
        result == can_satisfy_all_guests(a as nat, b as nat, n as nat, m as nat),
        result ==> ((a as nat) + (b as nat) >= (n as nat) + (m as nat) && (m as nat) <= min(a as nat, b as nat)),
        !result ==> ((a as nat) + (b as nat) < (n as nat) + (m as nat) || (m as nat) > min(a as nat, b as nat)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute result with runtime ops and prove equivalence using proof block */
    let sum_ab_u16: u16 = (a as u16) + (b as u16);
    let sum_nm_u16: u16 = (n as u16) + (m as u16);
    let runtime_min_u8: u8 = if a <= b { a } else { b };
    let result: bool = (sum_ab_u16 >= sum_nm_u16) && (m <= runtime_min_u8);

    proof {
        let na: nat = a as nat;
        let nb: nat = b as nat;
        let nn: nat = n as nat;
        let nm: nat = m as nat;

        lemma_min_equiv(na, nb);

        assert(((a as u16) + (b as u16)) as nat == na + nb);
        assert(((n as u16) + (m as u16)) as nat == nn + nm);
        assert(((a as u16) + (b as u16) >= (n as u16) + (m as u16)) == (na + nb >= nn + nm));
        assert((if a <= b { a } else { b }) as nat == min(na, nb));
        assert((m as nat) == nm);
        assert((m <= runtime_min_u8) == (nm <= min(na, nb)));
        assert(result == ((na + nb >= nn + nm) && (nm <= min(na, nb))));
        assert(result == can_satisfy_all_guests(na, nb, nn, nm));

        if result {
            assert(na + nb >= nn + nm && nm <= min(na, nb));
        } else {
            if !(na + nb >= nn + nm) {
                assert(na + nb < nn + nm || nm > min(na, nb));
            } else {
                assert(!(nm <= min(na, nb)));
                assert(nm > min(na, nb));
                assert(na + nb < nn + nm || nm > min(na, nb));
            }
        }
    }

    result
}

// </vc-code>


}

fn main() {}