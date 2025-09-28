// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn has_children(node: int, parents: Seq<int>, n: int) -> bool
    recommends 0 <= node < n, n >= 3, parents.len() == n - 1
{
    exists|i: int| 0 <= i < n - 1 && parents[i] - 1 == node
}

spec fn count_leaf_children(node: int, parents: Seq<int>, n: int) -> int
    recommends 0 <= node < n, n >= 3, parents.len() == n - 1
{
    (Set::new(|i: int| 0 <= i < n - 1 && parents[i] - 1 == node && !has_children(i + 1, parents, n))).len() as int
}

spec fn valid_input(n: int, parents: Seq<int>) -> bool
{
    n >= 3 && parents.len() == n - 1 && 
    (forall|i: int| 0 <= i < n - 1 ==> #[trigger] parents[i] >= 1 && parents[i] <= i + 1)
}

spec fn is_spruce(n: int, parents: Seq<int>) -> bool
    recommends valid_input(n, parents)
{
    forall|node: int| 0 <= node < n && has_children(node, parents, n) ==> 
        count_leaf_children(node, parents, n) >= 3
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma definition syntax by removing duplicate 'lemma' keyword */
fn lemma_no_counterexample_implies_forall(n: int, parents: Seq<int>)
    requires
        valid_input(n, parents),
        forall|node: int| 0 <= node < n && has_children(node, parents, n) ==> count_leaf_children(node, parents, n) >= 3,
    ensures
        is_spruce(n, parents)
{
}

fn count_children_with_property(node: i8, parents: &Vec<i8>, n: i8) -> (count: i8)
    requires
        0 <= node < n,
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
    ensures
        count >= 0,
        count == count_leaf_children(node as int, parents@.map_values(|x: i8| x as int), n as int),
{
    let mut count = 0;
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            count >= 0,
            count == (Set::new(|j: int| 0 <= j < i && parents@[j] - 1 == node as int && !has_children(j + 1, parents@.map_values(|x: i8| x as int), n as int))).len() as i8,
    {
        if parents[i as usize] - 1 == node {
            let child = i + 1;
            let mut has_child = false;
            let mut j = 0;
            while j < n - 1
                invariant
                    0 <= j <= n - 1,
                    has_child == exists|k: int| 0 <= k < j && parents@[k] - 1 == child as int,
            {
                if parents[j as usize] - 1 == child {
                    has_child = true;
                }
                j += 1;
            }
            if !has_child {
                count += 1;
            }
        }
        i += 1;
    }
    count
}

fn node_has_children(node: i8, parents: &Vec<i8>, n: i8) -> (result: bool)
    requires
        0 <= node < n,
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
    ensures
        result == has_children(node as int, parents@.map_values(|x: i8| x as int), n as int),
{
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            (exists|j: int| 0 <= j < i && parents@[j] - 1 == node as int) == false,
    {
        if parents[i as usize] - 1 == node {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, parents: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
    ensures 
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
        result@ == seq!['Y', 'e', 's'] <==> is_spruce(n as int, parents@.map_values(|x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed function call to use proof block */
    let mut node = 0;
    while node < n
        invariant
            0 <= node <= n,
            forall|i: int| 0 <= i < node && has_children(i, parents@.map_values(|x: i8| x as int), n as int) ==> 
                count_leaf_children(i, parents@.map_values(|x: i8| x as int), n as int) >= 3,
    {
        let has_child = node_has_children(node, &parents, n);
        if has_child {
            let leaf_count = count_children_with_property(node, &parents, n);
            if leaf_count < 3 {
                return "No".to_string();
            }
        }
        node += 1;
    }
    proof {
        lemma_no_counterexample_implies_forall(n as int, parents@.map_values(|x: i8| x as int));
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}