// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn count_distinct_colors(a: int, b: int, c: int) -> int {
    if a == b && b == c { 1 }
    else if a == b || b == c || a == c { 2 }
    else { 3 }
}

spec fn all_same(a: int, b: int, c: int) -> bool {
    a == b && b == c
}

spec fn exactly_two_same(a: int, b: int, c: int) -> bool {
    (a == b && b != c) || (b == c && a != b) || (a == c && a != b)
}

spec fn all_different(a: int, b: int, c: int) -> bool {
    a != b && b != c && a != c
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_distinct_colors_cases(a: int, b: int, c: int)
    requires
        valid_input(a, b, c)
    ensures
        count_distinct_colors(a, b, c) == 1 <==> all_same(a, b, c),
        count_distinct_colors(a, b, c) == 2 <==> exactly_two_same(a, b, c),
        count_distinct_colors(a, b, c) == 3 <==> all_different(a, b, c)
{
    /* helper modified by LLM (iteration 4): Complete proof with proper case analysis */
    reveal(count_distinct_colors);
    reveal(all_same);
    reveal(exactly_two_same);
    reveal(all_different);
    
    if a == b && b == c {
        assert(count_distinct_colors(a, b, c) == 1);
        assert(all_same(a, b, c));
    } else if a == b {
        assert(count_distinct_colors(a, b, c) == 2);
        assert(exactly_two_same(a, b, c));
    } else if b == c {
        assert(count_distinct_colors(a, b, c) == 2);
        assert(exactly_two_same(a, b, c));
    } else if a == c {
        assert(count_distinct_colors(a, b, c) == 2);
        assert(exactly_two_same(a, b, c));
    } else {
        assert(count_distinct_colors(a, b, c) == 3);
        assert(all_different(a, b, c));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        1 <= result as int <= 3,
        result as int == count_distinct_colors(a as int, b as int, c as int),
        result as int == 1 <==> all_same(a as int, b as int, c as int),
        result as int == 2 <==> exactly_two_same(a as int, b as int, c as int),
        result as int == 3 <==> all_different(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Remove unclosed delimiter and add proof call */
    proof {
        lemma_count_distinct_colors_cases(a as int, b as int, c as int);
    }
    
    if a == b && b == c {
        1
    } else if a == b || b == c || a == c {
        2
    } else {
        3
    }
}
// </vc-code>


}

fn main() {}