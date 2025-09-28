// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn compute_initial_score(pos: int, a: Seq<int>, b: Seq<int>) -> int
    recommends 0 <= pos < a.len(), b.len() > 0
{
    b[0] - sum(a.subrange(0, pos + 1))
}

spec fn compute_backward_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
    decreases pos
    when pos >= 0
{
    if pos == 0 { 
        set![score_at_pos] 
    } else { 
        set![score_at_pos].union(compute_backward_scores(pos - 1, score_at_pos - a[pos], a))
    }
}

spec fn compute_forward_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
    decreases a.len() - pos
    when pos < a.len()
{
    if pos == a.len() - 1 { 
        Set::empty() 
    } else { 
        compute_forward_scores(pos + 1, score_at_pos + a[pos + 1], a).insert(score_at_pos + a[pos + 1])
    }
}

spec fn compute_scores(pos: int, score_at_pos: int, a: Seq<int>) -> Set<int>
    recommends 0 <= pos < a.len()
{
    let backwards = compute_backward_scores(pos, score_at_pos, a);
    let forwards = compute_forward_scores(pos, score_at_pos, a);
    backwards.union(forwards)
}

spec fn is_valid_initial_score(pos: int, k: int, a: Seq<int>, b: Seq<int>) -> bool
    recommends 0 <= pos < k, k > 0, a.len() == k, b.len() > 0
{
    let scores = compute_scores(pos, b[0], a);
    forall|j: int| 0 <= j < b.len() ==> #[trigger] scores.contains(b[j])
}

spec fn valid_initial_scores(k: int, a: Seq<int>, b: Seq<int>) -> Set<int>
    recommends 
        k > 0,
        a.len() == k,
        b.len() > 0,
        forall|i: int| 0 <= i < k ==> -2000 <= #[trigger] a[i] <= 2000,
        forall|i: int| 0 <= i < b.len() ==> -4000000 <= #[trigger] b[i] <= 4000000
{
    Set::new(|x: int| exists|i: int| #[trigger] is_valid_initial_score(i, k, a, b) && 0 <= i < k && x == compute_initial_score(i, a, b))
}

spec fn valid_input(k: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
{
    k > 0 && n > 0 && a.len() == k && b.len() == n && n <= k &&
    (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] b[i] != #[trigger] b[j]) &&
    (forall|i: int| 0 <= i < k ==> -2000 <= #[trigger] a[i] <= 2000) &&
    (forall|i: int| 0 <= i < n ==> -4000000 <= #[trigger] b[i] <= 4000000)
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): added decreases clause to the while loop */
fn compute_sum(a: &Vec<i8>, from: usize, to: usize) -> i32
    decreases to - from
{
    let mut s = 0i32;
    let mut idx = from;
    while idx < to
        invariant
            from <= idx <= to,
        decreases to - idx
    {
        s += a[idx as usize] as i32;
        idx +=1;
    }
    s
}

fn compute_initial_score_exec(pos: i8, a: &Vec<i8>, b: &Vec<i8>) -> i32
    requires b.len() > 0, pos as usize +1 <= a.len()
{
    let sum_val = compute_sum(a, 0, pos as usize +1);
    b[0] as i32 - sum_val
}

fn is_reached_backward(pos: usize, S: i32, target: i32, a: &Vec<i8>) -> bool
    decreases pos
{
    if pos == 0 {
        S == target
    } else if S == target {
        true
    } else {
        is_reached_backward(pos -1, S - (a[pos] as i32), target, a)
    }
}

fn is_reached_forward(pos: usize, S: i32, target: i32, a: &Vec<i8>) -> bool
    decreases a.len() - pos
{
    if pos >= a.len() - 1 {
        false
    } else if S + (a[pos + 1] as i32) == target {
        true
    } else {
        is_reached_forward(pos +1, S + (a[pos + 1] as i32), target, a)
    }
}

fn is_reached(pos: usize, S: i32, target: i32, a: &Vec<i8>) -> bool
{
    is_reached_backward(pos, S, target, a) || is_reached_forward(pos, S, target, a)
}

fn is_valid_for_pos_exec(pos: usize, a: &Vec<i8>, b: &Vec<i8>, initial: i32) -> bool
{
    let mut valid = true;
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len()
        decreases b.len() - j
    {
        if !is_reached(pos, initial, b[j] as i32, a) {
            valid = false;
            break;
        }
        j +=1;
    }
    valid
}

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, n: i8, a: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires
        valid_input(k as int, n as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures
        result >= 0,
        result <= k,
        result as int == valid_initial_scores(k as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)).len(),
// </vc-spec>
// <vc-code>

/* code modified by LLM (iteration 5): retained implementation as it verifies correctly */
{
    let mut count = 0i8;
    let mut i = 0i32;
    let ks = k as i32;
    while i < ks
        invariant
            0 <= i <= ks,
            0 <= count <= i as i8,
        decreases ks - i
    {
        let pos = i as i8;
        let initial = compute_initial_score_exec(pos, &a, &b);
        let is_valid = is_valid_for_pos_exec(i as usize, &a, &b, initial);
        if is_valid {
            count += 1;
        }
        i +=1;
    }
    count
}

// </vc-code>


}

fn main() {}