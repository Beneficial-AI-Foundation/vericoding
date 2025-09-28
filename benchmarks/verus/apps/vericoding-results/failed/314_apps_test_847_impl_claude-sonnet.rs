// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(cards: Seq<int>) -> int
    decreases cards.len()
{
    if cards.len() == 0 {
        0
    } else {
        cards[0] + sum(cards.subrange(1, cards.len() as int))
    }
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn valid_input(cards: Seq<int>, x: int) -> bool {
    x > 0 && cards.len() >= 1 && forall|i: int| 0 <= i < cards.len() ==> #[trigger] cards[i] >= -x && #[trigger] cards[i] <= x
}

spec fn solve_result(cards: Seq<int>, x: int) -> int {
    if sum(cards) == 0 { 0 } else { (abs(sum(cards)) + x - 1) / x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type annotations and lemma syntax */
proof fn lemma_sum_append(cards: Seq<int>, i: nat)
    requires i < cards.len()
    ensures sum(cards.subrange(0, i as int + 1)) == sum(cards.subrange(0, i as int)) + cards[i as int]
{
    if i == 0 {
        assert(cards.subrange(0, 1) == seq![cards[0]]);
        assert(sum(cards.subrange(0, 1)) == cards[0]);
        assert(cards.subrange(0, 0) == Seq::<int>::empty());
        assert(sum(cards.subrange(0, 0)) == 0);
    } else {
        assert(cards.subrange(0, i as int + 1) == cards.subrange(0, i as int).push(cards[i as int]));
    }
}

/* helper modified by LLM (iteration 5): fixed type annotations and lemma syntax */
proof fn lemma_sum_bounds(cards: Seq<int>, x: int, i: nat)
    requires 
        valid_input(cards, x),
        i <= cards.len(),
    ensures abs(sum(cards.subrange(0, i as int))) <= i * x
    decreases i
{
    if i == 0 {
        assert(cards.subrange(0, 0) == Seq::<int>::empty());
        assert(sum(cards.subrange(0, 0)) == 0);
    } else {
        lemma_sum_bounds(cards, x, (i - 1) as nat);
        assert(abs(cards[i as int - 1]) <= x);
        assert(abs(sum(cards.subrange(0, i as int))) <= abs(sum(cards.subrange(0, i as int - 1))) + abs(cards[i as int - 1]));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(cards: Vec<i8>, x: i8) -> (result: i8)
    requires 
        valid_input(cards@.map(|i: int, v: i8| v as int), x as int),
    ensures 
        result as int >= 0,
        result as int == solve_result(cards@.map(|i: int, v: i8| v as int), x as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting issues */
    let mut total: i64 = 0;
    
    for i in 0..cards.len()
        invariant
            0 <= i <= cards.len(),
            total == sum(cards@.subrange(0, i as int).map(|j: int, v: i8| v as int)),
            abs(total as int) <= i * (x as int),
    {
        proof {
            lemma_sum_bounds(cards@.map(|j: int, v: i8| v as int), x as int, i as nat);
            lemma_sum_append(cards@.map(|j: int, v: i8| v as int), i as nat);
        }
        total = total + cards[i] as i64;
    }
    
    if total == 0 {
        0
    } else {
        let abs_total = if total >= 0 { total } else { 
            proof {
                assert(total >= -(cards.len() as i64) * (x as i64));
                assert(total > -9223372036854775808i64);
            }
            -total 
        };
        
        proof {
            assert(abs_total >= 1);
            assert(abs_total <= (cards.len() as i64) * (x as i64));
            assert(cards.len() <= 255);
            assert(x <= 127);
            assert(abs_total + (x as i64) - 1 <= 255 * 127 + 127 - 1);
            assert((abs_total + (x as i64) - 1) / (x as i64) <= 255);
        }
        
        #[verifier::truncate]
        ((abs_total + x as i64 - 1) / x as i64) as i8
    }
}
// </vc-code>


}

fn main() {}