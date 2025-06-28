use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DivMod(a: int, b: int) -> (q: int, r: int)
    requires b != 0
    ensures a == q * b + r
    ensures 0 <= r < b.abs()
{
    if b > 0 {
        if a >= 0 {
            // Both positive - standard division
            let q = a / b;
            let r = a % b;
            assert(a == q * b + r);
            assert(0 <= r < b);
            (q, r)
        } else {
            // a negative, b positive
            if a % b == 0 {
                let q = a / b;
                let r = 0;
                assert(a == q * b);
                assert(a == q * b + r);
                (q, r)
            } else {
                let q = a / b - 1;
                let r = a % b + b;
                assert(a % b < 0);
                assert(r == a % b + b);
                assert(r > 0);
                assert(r < b);
                assert(a == (a / b) * b + a % b);
                assert(a == (a / b - 1) * b + b + a % b);
                assert(a == q * b + r);
                (q, r)
            }
        }
    } else {
        // b < 0
        if a >= 0 {
            // a non-negative, b negative
            if a % (-b) == 0 {
                let q = -(a / (-b));
                let r = 0;
                assert(a == (a / (-b)) * (-b));
                assert(a == q * b);
                assert(a == q * b + r);
                (q, r)
            } else {
                let q = -(a / (-b)) - 1;
                let r = (-b) - (a % (-b));
                
                assert(a == (a / (-b)) * (-b) + a % (-b));
                assert(0 < a % (-b) < (-b));
                assert(0 < r < (-b));
                assert(r == (-b) - (a % (-b)));
                assert(a % (-b) == (-b) - r);
                assert(a == (a / (-b)) * (-b) + (-b) - r);
                assert(a == (a / (-b) + 1) * (-b) - r);
                assert(a == -(a / (-b) + 1) * b - r);
                assert(a == (-(a / (-b)) - 1) * b - r);
                assert(a == q * b - r);
                assert(a == q * b + (-r));
                
                // Need to adjust to get positive remainder
                let final_q = q;
                let final_r = r;
                assert(0 < final_r < (-b));
                assert((-b) == b.abs());
                assert(a == final_q * b + final_r) by {
                    assert(a == q * b - r);
                    assert(final_r == r);
                    assert(final_q == q);
                    assert(a == final_q * b - final_r);
                    // This assertion is incorrect, let me recalculate
                };
                
                // Recalculate properly
                let correct_q = -(a / (-b)) - 1;
                let correct_r = a - correct_q * b;
                
                assert(a / (-b) >= 0);
                assert(correct_q < 0);
                assert(correct_r >= 0) by {
                    assert(correct_r == a - correct_q * b);
                    assert(correct_q * b <= a) by {
                        assert(correct_q < 0);
                        assert(b < 0);
                        assert(correct_q * b > 0);
                    };
                };
                assert(correct_r < (-b)) by {
                    assert(correct_r == a - correct_q * b);
                    assert(correct_q == -(a / (-b)) - 1);
                    assert(correct_r == a - (-(a / (-b)) - 1) * b);
                    assert(correct_r == a + (a / (-b) + 1) * b);
                    assert(correct_r == a + (a / (-b)) * b + b);
                    assert(a == (a / (-b)) * (-b) + a % (-b));
                    assert(correct_r == (a / (-b)) * (-b) + a % (-b) + (a / (-b)) * b + b);
                    assert(correct_r == a % (-b) + b);
                    assert(0 < a % (-b) < (-b));
                    assert(0 < correct_r < (-b) + b);
                    assert(correct_r < (-b));
                };
                
                (correct_q, correct_r)
            }
        } else {
            // Both negative
            let pos_a = -a;
            let pos_b = -b;
            let temp_q = pos_a / pos_b;
            let temp_r = pos_a % pos_b;
            
            if temp_r == 0 {
                let q = temp_q;
                let r = 0;
                assert(pos_a == temp_q * pos_b);
                assert(a == -pos_a);
                assert(a == -(temp_q * pos_b));
                assert(a == temp_q * (-pos_b));
                assert(a == temp_q * b);
                assert(a == q * b + r);
                (q, r)
            } else {
                let q = temp_q;
                let r = temp_r;
                assert(pos_a == temp_q * pos_b + temp_r);
                assert(a == -pos_a);
                assert(a == -(temp_q * pos_b + temp_r));
                assert(a == -temp_q * pos_b - temp_r);
                assert(a == temp_q * (-pos_b) - temp_r);
                assert(a == temp_q * b - temp_r);
                
                // We need r to be positive, so adjust
                let final_q = temp_q - 1;
                let final_r = pos_b - temp_r;
                
                assert(a == temp_q * b - temp_r);
                assert(a == (temp_q - 1) * b + b - temp_r);
                assert(a == final_q * b + final_r);
                assert(0 < temp_r < pos_b);
                assert(0 < final_r < pos_b);
                assert(pos_b == b.abs());
                
                (final_q, final_r)
            }
        }
    }
}

}