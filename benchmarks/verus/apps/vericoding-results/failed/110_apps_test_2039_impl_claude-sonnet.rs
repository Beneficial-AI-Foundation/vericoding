// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n
}

spec fn count_local_extrema(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    Set::<int>::new(|i: int| 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))).len() as int
}

spec fn is_local_extremum(a: Seq<int>, i: int) -> bool
    recommends 0 <= i < a.len()
{
    1 <= i < a.len() - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix assertions for proper Set reasoning */
proof fn lemma_count_local_extrema_properties(n: int, a: Seq<int>)
    requires valid_input(n, a)
    ensures count_local_extrema(n, a) >= 0,
            n <= 2 ==> count_local_extrema(n, a) == 0,
            n > 2 ==> count_local_extrema(n, a) <= n - 2
{
    if n <= 2 {
        if n == 1 {
            assert(forall|i: int| !(1 <= i < n - 1));
        } else if n == 2 {
            assert(forall|i: int| !(1 <= i < n - 1));
        }
    } else {
        let extrema_set = Set::<int>::new(|i: int| 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1])));
        let valid_indices = Set::<int>::new(|i: int| 1 <= i < n - 1);
        assert(extrema_set.subset_of(valid_indices));
        assert(extrema_set.len() <= valid_indices.len());
        assert(valid_indices.finite());
        assert(extrema_set.finite());
    }
}

proof fn lemma_extrema_equivalence(n: int, a: Seq<int>, count: int)
    requires 
        valid_input(n, a),
        count >= 0,
        count <= n - 2
    ensures
        forall|i: int| 1 <= i < n - 1 ==> (is_local_extremum(a, i) <==> ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1])))
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        result >= 0,
        n <= 2 ==> result == 0,
        n > 2 ==> result <= n - 2,
        result as int == count_local_extrema(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix index bounds and loop invariant */
    proof {
        lemma_count_local_extrema_properties(n as int, a@.map_values(|x: i8| x as int));
    }
    
    if n <= 2 {
        return 0;
    }
    
    let mut count: i8 = 0;
    let mut i: usize = 1;
    
    while i < (n as usize - 1)
        invariant
            i <= n as usize - 1,
            count >= 0,
            count <= i as i8,
            i < a@.len(),
            count as int == Set::<int>::new(|j: int| 1 <= j < i as int && is_local_extremum(a@.map_values(|x: i8| x as int), j)).len() as int
        decreases (n as usize - 1) - i
    {
        assert(i + 1 < a@.len());
        assert(i >= 1);
        
        let is_max = a[i] > a[i-1] && a[i] > a[i+1];
        let is_min = a[i] < a[i-1] && a[i] < a[i+1];
        
        if is_max || is_min {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_extrema_equivalence(n as int, a@.map_values(|x: i8| x as int), count as int);
    }
    
    count
}
// </vc-code>


}

fn main() {}