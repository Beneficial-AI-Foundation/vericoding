use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_count_equal_numbers_properties(a: int, b: int, c: int, count: int)
    requires
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
    ensures
        (count == 0) == false,
        (count == 1) == (a != b && a != c && b != c),
{
}

spec fn count_equal_spec(a: int, b: int, c: int) -> int {
    if a == b && b == c {
        3
    } else if (a == b) || (b == c) || (a == c) {
        2
    } else {
        1
    }
}

proof fn lemma_count_equal_spec_consistent(a: int, b: int, c: int)
    ensures
        count_equal_spec(a, b, c) >= 1 && count_equal_spec(a, b, c) <= 3,
        (count_equal_spec(a, b, c) == 3) <==> (a == b && b == c),
        (count_equal_spec(a, b, c) == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count_equal_spec(a, b, c) == 1) <==> (a != b && b != c && a != c),
{
}
// </vc-helpers>

// <vc-spec>
fn count_equal_numbers(a: i32, b: i32, c: i32) -> (count: i32)
    ensures 
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_count_equal_spec_consistent(a as int, b as int, c as int);
    }
    
    let mut count: i32 = 0;
    
    if a == b {
        if b == c {
            count = 3;
        } else {
            count = 2;
        }
    } else if b == c {
        count = 2;
    } else if a == c {
        count = 2;
    } else {
        count = 1;
    }
    
    proof {
        lemma_count_equal_numbers_properties(a as int, b as int, c as int, count as int);
    }
    
    count
}
// </vc-code>

fn main() {}

}