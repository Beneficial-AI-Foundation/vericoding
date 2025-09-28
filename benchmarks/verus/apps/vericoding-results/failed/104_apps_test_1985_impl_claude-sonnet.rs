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
proof fn lemma_sum_subrange(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures sum(s.subrange(i, j)) == if i == j { 0 } else { s[i] + sum(s.subrange(i + 1, j)) }
    decreases j - i
{
    if i == j {
        assert(s.subrange(i, j).len() == 0);
    } else {
        assert(s.subrange(i, j)[0] == s[i]);
        assert(s.subrange(i, j).subrange(1, (j - i) as int) =~= s.subrange(i + 1, j));
    }
}

proof fn lemma_compute_scores_finite(pos: int, score_at_pos: int, a: Seq<int>)
    requires 0 <= pos < a.len()
    ensures compute_scores(pos, score_at_pos, a).finite()
    decreases a.len()
{
    lemma_backward_scores_finite(pos, score_at_pos, a);
    lemma_forward_scores_finite(pos, score_at_pos, a);
}

proof fn lemma_backward_scores_finite(pos: int, score_at_pos: int, a: Seq<int>)
    requires 0 <= pos < a.len()
    ensures compute_backward_scores(pos, score_at_pos, a).finite()
    decreases pos
{
    if pos == 0 {
        assert(compute_backward_scores(pos, score_at_pos, a) == set![score_at_pos]);
    } else {
        lemma_backward_scores_finite(pos - 1, score_at_pos - a[pos], a);
    }
}

proof fn lemma_forward_scores_finite(pos: int, score_at_pos: int, a: Seq<int>)
    requires 0 <= pos < a.len()
    ensures compute_forward_scores(pos, score_at_pos, a).finite()
    decreases a.len() - pos
{
    if pos == a.len() - 1 {
        assert(compute_forward_scores(pos, score_at_pos, a) == Set::<int>::empty());
    } else {
        lemma_forward_scores_finite(pos + 1, score_at_pos + a[pos + 1], a);
    }
}

proof fn lemma_valid_initial_scores_finite(k: int, a: Seq<int>, b: Seq<int>)
    requires k > 0, a.len() == k, b.len() > 0
    ensures valid_initial_scores(k, a, b).finite()
{
    let s = valid_initial_scores(k, a, b);
    assert(s.subset_of(Set::new(|x: int| exists|i: int| 0 <= i < k && x == compute_initial_score(i, a, b))));
    lemma_initial_scores_bounded(k, a, b);
}

/* helper modified by LLM (iteration 5): added trigger annotation to fix quantifier error */
proof fn lemma_initial_scores_bounded(k: int, a: Seq<int>, b: Seq<int>)
    requires k > 0, a.len() == k, b.len() > 0
    ensures forall|i: int| 0 <= i < k ==> -4002000 <= #[trigger] compute_initial_score(i, a, b) <= 4002000
{
}

fn sum_prefix(a: &Vec<i8>, end: i8) -> (result: i8)
    requires 0 <= end < a.len()
    ensures result as int == sum(a@.map_values(|x: i8| x as int).subrange(0, (end + 1) as int))
{
    let mut s = 0i8;
    let mut j = 0i8;
    
    while j <= end
        invariant
            0 <= j <= end + 1,
            s as int == sum(a@.map_values(|x: i8| x as int).subrange(0, j as int)),
        decreases end - j
    {
        s = s + a[j as usize];
        j = j + 1;
    }
    
    s
}

fn is_valid_position(pos: i8, score_at_pos: i8, a: &Vec<i8>, b: &Vec<i8>) -> (result: bool)
    requires
        0 <= pos < a.len(),
        b.len() > 0,
    ensures
        result == is_valid_initial_score(pos as int, a.len() as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
{
    let mut j = 0i8;
    
    while j < b.len() as i8
        invariant
            0 <= j <= b.len(),
            forall|idx: int| 0 <= idx < j ==> #[trigger] compute_scores(pos as int, score_at_pos as int, a@.map_values(|x: i8| x as int)).contains(#[trigger] b@.map_values(|x: i8| x as int)[idx]),
        decreases b.len() - j
    {
        if !can_reach_score(pos, score_at_pos, b[j as usize], a) {
            return false;
        }
        j = j + 1;
    }
    
    true
}

fn can_reach_score(pos: i8, current_score: i8, target_score: i8, a: &Vec<i8>) -> (result: bool)
    requires 0 <= pos < a.len()
    ensures result == compute_scores(pos as int, current_score as int, a@.map_values(|x: i8| x as int)).contains(target_score as int)
{
    if current_score == target_score {
        return true;
    }
    
    let mut score = current_score;
    let mut i = pos;
    
    while i > 0
        invariant
            0 <= i <= pos,
        decreases i
    {
        score = score - a[i as usize];
        if score == target_score {
            return true;
        }
        i = i - 1;
    }
    
    score = current_score;
    i = pos;
    
    while i < a.len() as i8 - 1
        invariant
            pos <= i < a.len(),
        decreases a.len() - i
    {
        i = i + 1;
        score = score + a[i as usize];
        if score == target_score {
            return true;
        }
    }
    
    false
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
{
    /* code modified by LLM (iteration 5): fixed type annotation for Set::empty() call */
    let mut count = 0i8;
    let mut i = 0i8;
    
    while i < k
        invariant
            0 <= i <= k,
            0 <= count <= i,
            count as int == Set::new(|x: int| exists|j: int| 0 <= j < i && #[trigger] is_valid_initial_score(j, k as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) && x == compute_initial_score(j, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))).len(),
        decreases k - i
    {
        let initial_score = b[0] - sum_prefix(&a, i);
        if is_valid_position(i, initial_score, &a, &b) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_valid_initial_scores_finite(k as int, a@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int));
    }
    
    count
}
// </vc-code>


}

fn main() {}