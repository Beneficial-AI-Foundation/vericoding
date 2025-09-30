// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn last_occurrence_helper(cafes: Seq<int>, cafe: int, pos: int) -> int
    decreases pos + 1
{
    if pos < 0 || pos >= cafes.len() { -1 }
    else if cafes[pos] == cafe { pos }
    else { last_occurrence_helper(cafes, cafe, pos - 1) }
}

spec fn last_occurrence_position(cafes: Seq<int>, cafe: int) -> int
{
    last_occurrence_helper(cafes, cafe, (cafes.len() - 1) as int)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_last_occurrence_helper(cafes: Seq<int>, cafe: int, pos: int, current: int)
    requires
        0 <= pos < cafes.len(),
        cafes[pos] == cafe,
        forall|j: int| pos < j < cafes.len() ==> cafes[j] != cafe,
        pos <= current < cafes.len(),
    ensures
        last_occurrence_helper(cafes, cafe, current) == pos,
    decreases current - pos
{
    if current > pos {
        lemma_last_occurrence_helper(cafes, cafe, pos, current - 1);
    }
}

proof fn lemma_last_occurrence(cafes: Seq<int>, cafe: int, pos: int)
    requires
        0 <= pos < cafes.len(),
        cafes[pos] == cafe,
        forall|j: int| pos < j < cafes.len() ==> cafes[j] != cafe,
    ensures
        last_occurrence_position(cafes, cafe) == pos,
{
    let len = cafes.len() as int;
    if len > 0 {
        lemma_last_occurrence_helper(cafes, cafe, pos, len - 1);
    }
}

/* helper modified by LLM (iteration 5): Fixed compilation error by replacing unreachable loop with a dummy return value `0`, and removed a faulty invariant. */
fn exec_last_occurrence_position(cafes: &Vec<i8>, cafe: i8) -> (pos: usize)
    requires
        cafes.len() > 0,
        cafes@.contains(cafe),
    ensures
        pos < cafes.len(),
        cafes@[pos as int] == cafe,
        (pos as int) == last_occurrence_position(cafes@.map(|_i, x: i8| x as int), cafe as int),
{
    let mut i = cafes.len();
    while i > 0
        invariant
            0 < i <= cafes.len(),
            cafes@.contains(cafe),
            forall|j: int| i <= j < cafes.len() ==> cafes@[j] != cafe,
        decreases i
    {
        i = i - 1;
        if cafes[i] == cafe {
            proof {
                let cafes_int = cafes@.map(|_i, x: i8| x as int);
                lemma_last_occurrence(cafes_int, cafe as int, i as int);
            }
            return i;
        }
    }
    proof {
        assert(false);
    }
    0
}
// </vc-helpers>

// <vc-spec>
fn solve(cafes: Vec<i8>) -> (mini: i8)
    requires
        cafes.len() > 0,
    ensures
        cafes@.contains(mini),
        forall|cafe: i8| #![auto] cafes@.contains(cafe) ==> last_occurrence_position(cafes@.map(|i, x: i8| x as int), mini as int) <= last_occurrence_position(cafes@.map(|i, x: i8| x as int), cafe as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No logical change; expecting fix in helper function to resolve verification. */
    let mut mini = cafes[0];
    let mut min_last_pos = exec_last_occurrence_position(&cafes, mini);

    let mut i: usize = 1;
    while i < cafes.len()
        invariant
            0 < i <= cafes.len(),
            cafes@.contains(mini),
            min_last_pos < cafes.len(),
            cafes@[min_last_pos as int] == mini,
            min_last_pos as int == last_occurrence_position(cafes@.map(|_i, x: i8| x as int), mini as int),
            forall|j: int| 0 <= j < i ==> 
                last_occurrence_position(cafes@.map(|_i, x: i8| x as int), mini as int) <=
                last_occurrence_position(cafes@.map(|_i, x: i8| x as int), cafes@[j] as int),
        decreases cafes.len() - i
    {
        let current_cafe = cafes[i];
        let current_last_pos = exec_last_occurrence_position(&cafes, current_cafe);

        if current_last_pos < min_last_pos {
            mini = current_cafe;
            min_last_pos = current_last_pos;
        }
        i = i + 1;
    }

    mini
}
// </vc-code>


}

fn main() {}