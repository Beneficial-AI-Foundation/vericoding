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
fn exec_has_children(node: i8, parents: &Vec<i8>, n: i8) -> (result: bool)
    requires
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
        0 <= node < n,
    ensures
        result == has_children(node as int, parents@.map_values(|x: i8| x as int), n as int),
{
    let mut i: usize = 0;
    while i < (n - 1) as usize
        invariant
            valid_input(n as int, parents@.map_values(|x: i8| x as int)),
            0 <= node < n,
            0 <= i <= (n - 1) as usize,
            forall|k: int| 0 <= k < i as int ==> (parents@.map_values(|x: i8| x as int))[k] - 1 != node as int,
        decreases (n - 1) as usize - i,
    {
        if parents[i] - 1 == node {
            return true;
        }
        i = i + 1;
    }
    return false;
}

fn exec_count_leaf_children(node: i8, parents: &Vec<i8>, n: i8) -> (result: i8)
    requires
        valid_input(n as int, parents@.map_values(|x: i8| x as int)),
        0 <= node < n,
    ensures
        result as int == count_leaf_children(node as int, parents@.map_values(|x: i8| x as int), n as int),
{
    let mut count: i8 = 0;
    let mut i: usize = 0;
    while i < (n - 1) as usize
        invariant
            valid_input(n as int, parents@.map_values(|x: i8| x as int)),
            0 <= node < n,
            0 <= i <= (n - 1) as usize,
            count as int == (Set::new(|k: int|
                0 <= k < i as int &&
                (parents@.map_values(|x: i8| x as int))[k] - 1 == node as int &&
                !has_children(k + 1, parents@.map_values(|x: i8| x as int), n as int)
            )).len() as int,
        decreases (n-1) as usize - i,
    {
        if parents[i] - 1 == node {
            let child = (i + 1) as i8;
            assert(0 <= child < n) by {
                assert(i < (n - 1) as usize);
                assert(i + 1 < n as usize);
            }
            let child_is_leaf = !exec_has_children(child, parents, n);
            if child_is_leaf {
                count = count + 1;
            }
        }
        i = i + 1;
    }
    return count;
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
/* code modified by LLM (iteration 5): Replaced unsupported String::from with vstd::string::new_strlit to fix compilation error. */
{
    let mut node: i8 = 0;
    while node < n
        invariant
            valid_input(n as int, parents@.map_values(|x: i8| x as int)),
            0 <= node <= n,
            forall|k: int| 0 <= k < node as int && has_children(k, parents@.map_values(|x: i8| x as int), n as int) ==> 
                count_leaf_children(k, parents@.map_values(|x: i8| x as int), n as int) >= 3,
        decreases n - node,
    {
        let has_c = exec_has_children(node, &parents, n);
        if has_c {
            let leaf_children_count = exec_count_leaf_children(node, &parents, n);
            if leaf_children_count < 3 {
                return vstd::string::new_strlit("No");
            }
        }
        node = node + 1;
    }
    return vstd::string::new_strlit("Yes");
}
// </vc-code>


}

fn main() {}