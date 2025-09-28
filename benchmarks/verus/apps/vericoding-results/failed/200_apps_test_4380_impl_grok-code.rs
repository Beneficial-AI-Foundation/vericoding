// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3
}

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

spec fn exists_odd_product(a: int, b: int) -> bool {
    valid_input(a, b) ==> exists|c: int| 1 <= c <= 3 && #[trigger] is_odd(a * b * c)
}

spec fn should_answer_yes(a: int, b: int) -> bool {
    valid_input(a, b) ==> (a != 2 && b != 2)
}
// </vc-preamble>

// <vc-helpers>
proof fn no_odd_product_if_two(a: int, b: int)
    requires
        valid_input(a, b),
        a == 2 || b == 2,
    ensures
        ! exists |c: int| 1 <= c <= 3 && #[trigger] is_odd(a * b * c)
{
    proof {
        assert forall |c: int| #[trigger] (1 <= c && c <= 3) ==> a * b * c % 2 == 0 by {
            assert(a * b % 2 == 0);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed type annotation for c to resolve compilation error */
proof fn should_answer_yes_equals_odd_product(a: int, b: int)
    requires valid_input(a, b)
    ensures should_answer_yes(a, b) <==> exists_odd_product(a, b)
{
    proof {
        if a == 2 || b == 2 {
            assert (should_answer_yes(a, b) == false);
            assert (forall |c: int| #[trigger] (1 <= c <= 3) ==> !is_odd(a * b * c)) by {
                proof {
                    assert(a * b % 2 == 0);
                }
            }
            assert (!exists_odd_product(a, b));
        } else {
            assert (should_answer_yes(a, b) == true);
            assert (exists |c: int| 1 <= c <= 3 && #[trigger] is_odd(a * b * c)) by {
                proof {
                    let c: int = 1;
                    assert(1 <= c && c <= 3);
                    assert(is_odd(a * b * c)) by {
                        assert ((a * b) % 2 == 1);
                    }
                }
            }
            assert (exists_odd_product(a, b));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): removed incorrect assume statement to correct verification */
    if a != 2i8 && b != 2i8 {
        "Yes"@
    } else {
        "No"@
    }
}
// </vc-code>


}

fn main() {}