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
    /* code modified by LLM (iteration 5): added trigger annotation for quantifier */
    let mut leaf_count: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            i <= n as usize,
            leaf_count.len() == i,
            forall|j: int| 0 <= j < i ==> leaf_count@[j] == 0i8,
        decreases n as usize - i
    {
        leaf_count.push(0i8);
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < (n - 1) as usize
        invariant
            i <= (n - 1) as usize,
            leaf_count.len() == n as usize,
            forall|j: int| 0 <= j < n as int ==> #[trigger] leaf_count@[j] >= 0 && leaf_count@[j] <= n,
        decreases (n - 1) as usize - i
    {
        let parent_idx = (parents[i] - 1) as usize;
        
        let mut is_leaf = true;
        let mut j: usize = 0;
        while j < (n - 1) as usize
            invariant
                j <= (n - 1) as usize,
                is_leaf <==> forall|k: int| 0 <= k < j ==> parents@[k] != (i + 1) as i8,
            decreases (n - 1) as usize - j
        {
            if parents[j] == (i + 1) as i8 {
                is_leaf = false;
            }
            j = j + 1;
        }
        
        if is_leaf {
            leaf_count.set(parent_idx, leaf_count[parent_idx] + 1);
        }
        i = i + 1;
    }
    
    let mut is_valid = true;
    let mut i: usize = 0;
    
    let ghost n_int = n as int;
    let ghost parents_int = parents@.map_values(|x: i8| x as int);
    
    while i < n as usize
        invariant
            i <= n as usize,
            is_valid <==> forall|j: int| 0 <= j < i ==> (!has_children(j, parents_int, n_int) || leaf_count@[j] >= 3),
        decreases n as usize - i
    {
        let mut has_child = false;
        let mut j: usize = 0;
        while j < (n - 1) as usize
            invariant
                j <= (n - 1) as usize,
                has_child <==> exists|k: int| 0 <= k < j && parents@[k] == (i + 1) as i8,
            decreases (n - 1) as usize - j
        {
            if parents[j] == (i + 1) as i8 {
                has_child = true;
            }
            j = j + 1;
        }
        
        if has_child && leaf_count[i] < 3 {
            is_valid = false;
        }
        i = i + 1;
    }
    
    if is_valid {
        return "Yes".to_string();
    } else {
        return "No".to_string();
    }
}
// </vc-code>


}

fn main() {}