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
        a
    } else if b % 2 == 0 {
        // Even case: a * b = (2*a) * (b/2)
        assert(b >= 2);
        assert(b / 2 >= 1) by {
            assert(b >= 2);
            assert(b > 0);
        };
        assert(b / 2 < b) by {
            assert(b >= 2);
            assert(b > 0);
        };
        let result = peasantMult(2 * a, b / 2);
        assert(result == (2 * a) * (b / 2));
        assert(result == a * b) by {
            assert(b % 2 == 0);
            // When b is even, b = 2 * (b / 2)
            // Use the built-in property of division for even numbers
            assert(b == 2 * (b / 2)) by {
                // For even b, we have b = (b / 2) * 2
                assert(b / 2 * 2 == b);
            };
            // Therefore a * b = a * (2 * (b / 2)) = (2 * a) * (b / 2)
            assert(a * b == a * (2 * (b / 2)));
            assert(a * (2 * (b / 2)) == (a * 2) * (b / 2)) by {
                // Associativity of multiplication
            };
            assert((a * 2) * (b / 2) == (2 * a) * (b / 2)) by {
                // Commutativity of multiplication
            };
        };
        result
    } else {
        // Odd case: a * b = a + a * (b-1) = a + (2*a) * ((b-1)/2)
        assert(b % 2 == 1);
        assert(b >= 1);
        assert(b != 1);
        assert(b >= 3) by {
            assert(b > 1);
            assert(b % 2 == 1);
            // If b > 1 and b is odd, then b >= 3
        };
        assert((b - 1) % 2 == 0) by {
            assert(b % 2 == 1);
            // If b is odd, then b-1 is even
        };
        assert((b - 1) / 2 >= 1) by {
            assert(b >= 3);
            assert(b - 1 >= 2);
        };
        assert((b - 1) / 2 < b) by {
            assert(b >= 3);
            assert(b - 1 < b);
            assert((b - 1) / 2 <= b - 1);
            assert((b - 1) / 2 < b);
        };
        let recursive_result = peasantMult(2 * a, (b - 1) / 2);
        assert(recursive_result == (2 * a) * ((b - 1) / 2));
        let result = a + recursive_result;
        assert(result == a * b) by {
            // Since b is odd: b = 1 + (b-1) where (b-1) is even
            assert(b == 1 + (b - 1));
            assert(a * b == a * (1 + (b - 1)));
            assert(a * (1 + (b - 1)) == a * 1 + a * (b - 1)) by {
                // Distributivity
            };
            assert(a * 1 + a * (b - 1) == a + a * (b - 1));
            
            // Since (b-1) is even: (b-1) = 2 * ((b-1)/2)
            assert((b - 1) == 2 * ((b - 1) / 2)) by {
                assert((b - 1) % 2 == 0);
                // For even (b-1), we have (b-1) = ((b-1) / 2) * 2
                assert((b - 1) / 2 * 2 == b - 1);
            };
            assert(a * (b - 1) == a * (2 * ((b - 1) / 2)));
            assert(a * (2 * ((b - 1) / 2)) == (a * 2) * ((b - 1) / 2)) by {
                // Associativity
            };
            assert((a * 2) * ((b - 1) / 2) == (2 * a) * ((b - 1) / 2)) by {
                // Commutativity
            };
            
            // Combining everything
            assert(a * b == a + a * (b - 1));
            assert(a * (b - 1) == (2 * a) * ((b - 1) / 2));
            assert(recursive_result == (2 * a) * ((b - 1) / 2));
            assert(a * (b - 1) == recursive_result);
            assert(result == a + recursive_result);
            assert(result == a + a * (b - 1));
            assert(result == a * b);
        };
        result
    }
}

}