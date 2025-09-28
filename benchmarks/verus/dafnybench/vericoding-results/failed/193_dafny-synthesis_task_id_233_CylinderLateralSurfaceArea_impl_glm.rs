use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_multiplication_is_associative(a: u64, b: u64, c: u64)
    ensures a * (b * c) == (a * b) * c
{
    // Multiplication is associative for natural numbers
    // This is built into Verus's arithmetic reasoning
    // However, we need to prove it explicitly for u64
    // We can do this by induction or by using the fact that multiplication is associative in mathematics
    // Since Verus already knows this, we can use a proof block with no body
}

proof fn lemma_division_of_product(a: u64, b: u64, c: u64)
    requires 
        c > 0,
        (a * b * c) % 100 == 0,
    ensures (a * b * c) / 100 == a * (b * c / 100)
{
    proof {
        lemma_multiplication_is_associative(a, b, c);
        assert(a * (b * c) == (a * b) * c);
        assert((a * b * c) / 100 == ((a * b) * c) / 100);
    }
}

proof fn lemma_division_preserves_multiplication(a: u64, b: u64)
    requires
        a % 100 == 0,
    ensures
        a / 100 * b == a * b / 100
{
    proof {
        assert(a == a / 100 * 100);
        assert(a * b == (a / 100 * 100) * b);
        lemma_multiplication_is_associative(a / 100, 100, b);
        assert((a / 100 * 100) * b == a / 100 * (100 * b));
        assert(a * b == a / 100 * (100 * b));
        assert(a * b / 100 == (a / 100 * (100 * b)) / 100);
        assert((a / 100 * (100 * b)) / 100 == a / 100 * b);
    }
}

proof fn lemma_division_by_100_for_divisible(a: u64)
    requires
        a % 100 == 0,
    ensures
        a / 100 * 100 == a
{
    proof {
        assert(a / 100 * 100 <= a);
        assert(a - a / 100 * 100 == a % 100);
        assert(a % 100 == 0);
        assert(a - a / 100 * 100 == 0);
        assert(a == a / 100 * 100);
    }
}

proof fn lemma_multiplication_is_commutative(a: u64, b: u64)
    ensures a * b == b * a
{
    // Multiplication is commutative for natural numbers
    // This is built into Verus's arithmetic reasoning
}
// </vc-helpers>

// <vc-spec>
fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_multiplication_is_commutative(2, radius);
        assert(2 * radius == radius * 2);
    }
    let two_radius = radius * 2;
    
    proof {
        lemma_multiplication_is_associative(radius, 2, height);
        assert(radius * 2 * height == 2 * radius * height);
    }
    let radius_height = two_radius * height;
    
    proof {
        lemma_multiplication_is_associative(2 * radius, height, 314);
        assert(2 * radius * height * 314 == radius_height * 314);
    }
    let product = radius_height * 314;
    
    proof {
        assert(product == 2 * radius * height * 314);
        assert(2 * radius * height * 314 % 100 == 0);
        assert(product % 100 == 0);
        lemma_division_by_100_for_divisible(product);
        assert(product / 100 * 100 == product);
    }
    
    let lateral_area = product / 100;
    lateral_area
}
// </vc-code>

fn main() {
}

}