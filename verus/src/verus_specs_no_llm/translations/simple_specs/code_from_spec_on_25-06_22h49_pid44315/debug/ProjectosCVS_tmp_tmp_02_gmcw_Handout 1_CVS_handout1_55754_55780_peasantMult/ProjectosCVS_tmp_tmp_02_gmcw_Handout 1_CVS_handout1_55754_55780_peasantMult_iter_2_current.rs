use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn peasantMult(a: int, b: int) -> (r: int)
    requires
        b > 0
    ensures
        r == a * b
    decreases b
{
    if b == 1 {
        assert(a * 1 == a);
        a
    } else if b % 2 == 0 {
        assert(b > 1);
        assert(b / 2 > 0);
        assert(b / 2 < b);
        assert(a * b == (2 * a) * (b / 2)) by {
            assert(a * b == a * (2 * (b / 2)));
            assert(a * (2 * (b / 2)) == (a * 2) * (b / 2));
            assert((a * 2) * (b / 2) == (2 * a) * (b / 2));
        };
        peasantMult(2 * a, b / 2)
    } else {
        assert(b > 1);
        assert(b % 2 == 1);
        assert((b - 1) / 2 > 0) by {
            assert(b >= 3);
            assert(b - 1 >= 2);
            assert((b - 1) / 2 >= 1);
        };
        assert((b - 1) / 2 < b) by {
            assert(b - 1 < b);
            assert((b - 1) / 2 <= b - 1);
            assert(b - 1 < b);
        };
        assert(a * b == a + (2 * a) * ((b - 1) / 2)) by {
            assert(b == 1 + (b - 1));
            assert(b - 1 == 2 * ((b - 1) / 2)) by {
                assert((b - 1) % 2 == 0);
            };
            assert(a * b == a * (1 + (b - 1)));
            assert(a * (1 + (b - 1)) == a + a * (b - 1));
            assert(a * (b - 1) == a * (2 * ((b - 1) / 2)));
            assert(a * (2 * ((b - 1) / 2)) == (a * 2) * ((b - 1) / 2));
            assert((a * 2) * ((b - 1) / 2) == (2 * a) * ((b - 1) / 2));
        };
        a + peasantMult(2 * a, (b - 1) / 2)
    }
}

}