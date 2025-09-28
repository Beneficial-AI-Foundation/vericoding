use vstd::prelude::*;

verus! {

spec fn is_peek(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

spec fn peek_sum(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i when 0 <= i <= v.len()
{
    if i == 0 {
        0
    } else {
        if is_peek(v, i - 1) {
            v[i - 1] + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        }
    }
}

// <vc-helpers>
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn running_max_holds(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i <= v.len()
{
    forall|j: int| 0 <= j < i ==> running_max(v, i) >= v@[j] as int
}

spec fn running_max(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i
{
    if i == 0 {
        -2147483648
    } else {
        max(running_max(v, i - 1), v@[i - 1] as int)
    }
}

proof fn lemma_running_max_properties(v: &Vec<i32>, i: int)
    requires
        0 <= i <= v.len(),
    ensures
        running_max_holds(v, i),
        i > 0 ==> running_max(v, i) == max(running_max(v, i - 1), v@[i - 1] as int),
    decreases i
{
    if i > 0 {
        lemma_running_max_properties(v, i - 1);
        assert forall|j: int| 0 <= j < i implies running_max(v, i) >= v@[j] as int by {
            if j < i - 1 {
                assert(running_max(v, i - 1) >= v@[j] as int);
                assert(running_max(v, i) >= running_max(v, i - 1));
            } else {
                assert(j == i - 1);
                assert(running_max(v, i) >= v@[i - 1] as int);
            }
        };
    }
}

proof fn lemma_peek_sum_relation(v: &Vec<i32>, i: int)
    requires
        0 <= i <= v.len(),
        running_max_holds(v, i),
    ensures
        peek_sum(v, i) == if i > 0 && running_max(v, i) == v@[i - 1] as int {
            v@[i - 1] as int + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        },
    decreases i
{
    reveal(peek_sum);
    if i > 0 {
        lemma_running_max_properties(v, i);
        assert(is_peek(v, i - 1) == (running_max(v, i) == v@[i - 1] as int)) by {
            assert forall|k: int| 0 <= k < i - 1 implies v@[i - 1] >= v@[k] by {
                lemma_running_max_properties(v, k + 1);
                lemma_running_max_properties(v, i);
                assert(running_max(v, i) >= running_max(v, k + 1));
                assert(running_max(v, k + 1) >= v@[k] as int);
            };
        };
    }
}

proof fn lemma_running_max_monotonic(v: &Vec<i32>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
        running_max_holds(v, j),
    ensures
        running_max(v, i) <= running_max(v, j),
    decreases j - i
{
    if i < j {
        lemma_running_max_monotonic(v, i, j - 1);
        lemma_running_max_properties(v, j);
        assert(running_max(v, j) >= running_max(v, j - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
    //Implement and verify an O(v.len()) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut current_max: i32 = -2147483648;
    let mut idx: usize = 0;
    
    proof {
        lemma_running_max_properties(v, 0);
    }
    
    while idx < v.len()
        invariant
            0 <= idx <= v.len(),
            current_max as int == running_max(v, idx as int),
            sum as int == peek_sum(v, idx as int),
            running_max_holds(v, idx as int),
        decreases v.len() - idx
    {
        let elem = v[idx];
        
        proof {
            lemma_running_max_properties(v, idx as int);
        }
        
        let prev_max = current_max;
        let mut new_max = current_max;
        if elem > current_max {
            new_max = elem;
        }
        
        proof {
            lemma_running_max_properties(v, (idx + 1) as int);
            lemma_peek_sum_relation(v, (idx + 1) as int);
            assert(running_max(v, (idx + 1) as int) == max(running_max(v, idx as int), elem as int));
        }
        
        if elem > current_max {
            current_max = elem;
            sum = sum + elem;
        }
        
        proof {
            assert(current_max as int == running_max(v, (idx + 1) as int));
            assert(sum as int == peek_sum(v, (idx + 1) as int));
        }
        
        idx = idx + 1;
    }
    sum
}
// </vc-code>

fn main() {}

}