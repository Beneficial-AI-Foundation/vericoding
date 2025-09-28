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
proof fn sum_bounds_lemma(cards: Seq<int>, x: int)
    requires
        valid_input(cards, x),
    ensures
        sum(cards) >= -(cards.len() * x),
        sum(cards) <= cards.len() * x,
    decreases cards.len()
{
    if cards.len() == 0 {
    } else {
        let rest = cards.subrange(1, cards.len() as int);
        assert(valid_input(rest, x));
        sum_bounds_lemma(rest, x);
    }
}

proof fn division_lemma(a: int, b: int)
    requires
        b > 0,
        a >= 0,
    ensures
        (a + b - 1) / b >= 0,
        (a + b - 1) / b <= a / b + 1,
{
}

/* helper modified by LLM (iteration 3): Keep spec function for specs only */
spec fn map_i8_to_int(cards: Seq<i8>) -> Seq<int> {
    cards.map(|i: int, v: i8| v as int)
}

fn compute_sum(cards: &Vec<i8>) -> (result: i32)
    requires
        cards.len() >= 1,
    ensures
        result == sum(map_i8_to_int(cards@)),
    decreases cards.len()
{
    let mut s: i32 = 0;
    let mut i: usize = 0;
    
    while i < cards.len()
        invariant
            0 <= i <= cards.len(),
            s == sum(map_i8_to_int(cards@).subrange(0, i as int)),
        decreases cards.len() - i
    {
        proof {
            let mapped = map_i8_to_int(cards@);
            let prev_sum = sum(mapped.subrange(0, i as int));
            let next_sum = sum(mapped.subrange(0, (i + 1) as int));
            assert(mapped.subrange(0, (i + 1) as int) =~= mapped.subrange(0, i as int).push(mapped[i as int]));
            assert(next_sum == prev_sum + mapped[i as int]);
        }
        s = s + (cards[i] as i32);
        i = i + 1;
    }
    
    assert(map_i8_to_int(cards@).subrange(0, cards.len() as int) =~= map_i8_to_int(cards@));
    s
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
    /* code modified by LLM (iteration 3): Avoid calling spec function in exec mode */
    proof {
        let mapped = cards@.map(|i: int, v: i8| v as int);
        assert(mapped =~= map_i8_to_int(cards@));
        sum_bounds_lemma(mapped, x as int);
    }
    
    let s = compute_sum(&cards);
    assert(s == sum(cards@.map(|i: int, v: i8| v as int)));
    
    if s == 0 {
        return 0;
    }
    
    let abs_s = if s >= 0 { s } else { -s };
    assert(abs_s == abs(s as int));
    
    let result = ((abs_s + (x as i32) - 1) / (x as i32)) as i8;
    
    proof {
        division_lemma(abs_s as int, x as int);
        assert(result >= 0);
        let mapped = cards@.map(|i: int, v: i8| v as int);
        assert(result as int == (abs(sum(mapped)) + x as int - 1) / (x as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}