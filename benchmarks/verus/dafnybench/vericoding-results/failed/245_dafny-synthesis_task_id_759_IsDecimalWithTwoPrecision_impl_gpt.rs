use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn exists_implies_guard(s: &str)
    ensures
        (exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2)
        ==> (s@.len() >= 3 && s@[s@.len() - 3] == '.')
{
    if exists|i: int| 0 <= i && i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2 {
        let i = choose|i: int| 0 <= i && i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2;
        let n = s@.len();
        assert(n - i - 1 == 2);
        assert(n - i == 3);
        assert(n == i + 3);
        assert(n >= 3);
        assert(n - 3 == i);
        assert(0 <= n - 3);
        assert(n - 3 < n);
        assert(s@[n - 3] == s@[i]);
        assert(s@[n - 3] == '.');
    }
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let n = s@.len();
    if n >= 3 {
        if s@[n - 3] == '.' {
            proof {
                let i = n - 3;
                assert(0 <= i);
                assert(i < n);
                assert(s@[i] == '.');
                assert(n - i - 1 == 2);
            }
            true
        } else {
            proof {
                exists_implies_guard(s);
            }
            false
        }
    } else {
        proof {
            exists_implies_guard(s);
        }
        false
    }
}
// </vc-code>

fn main() {
}

}