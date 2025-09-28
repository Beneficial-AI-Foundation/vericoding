// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<int>>) -> bool {
    grid.len() > 0 && forall|i: int| #![auto] 0 <= i < grid.len() ==> grid[i].len() > 0
}

spec fn seq_min(s: Seq<int>) -> int 
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { 
        s[0]
    } else {
        let tail_min = seq_min(s.drop_first());
        if s[0] <= tail_min { 
            s[0]
        } else { 
            tail_min
        }
    }
}

spec fn seq_max(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { 
        s[0]
    } else {
        let tail_max = seq_max(s.drop_first());
        if s[0] >= tail_max { 
            s[0]
        } else { 
            tail_max
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed take lemmas to properly handle recursive structure and invariant violations */
proof fn lemma_seq_min_in_bounds(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> seq_min(s) <= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(seq_min(s) == s[0]);
    } else {
        let tail_min = seq_min(s.drop_first());
        lemma_seq_min_in_bounds(s.drop_first());
        assert(forall|i: int| 0 <= i < s.drop_first().len() ==> tail_min <= s.drop_first()[i]);
        assert(forall|i: int| 1 <= i < s.len() ==> tail_min <= s[i]);
        if s[0] <= tail_min {
            assert(seq_min(s) == s[0]);
        } else {
            assert(seq_min(s) == tail_min);
            assert(forall|i: int| 1 <= i < s.len() ==> seq_min(s) <= s[i]);
        }
    }
}

proof fn lemma_seq_max_in_bounds(s: Seq<int>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> s[i] <= seq_max(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(seq_max(s) == s[0]);
    } else {
        let tail_max = seq_max(s.drop_first());
        lemma_seq_max_in_bounds(s.drop_first());
        assert(forall|i: int| 0 <= i < s.drop_first().len() ==> s.drop_first()[i] <= tail_max);
        assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= tail_max);
        if s[0] >= tail_max {
            assert(seq_max(s) == s[0]);
        } else {
            assert(seq_max(s) == tail_max);
            assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= seq_max(s));
        }
    }
}

proof fn lemma_seq_min_take(s: Seq<int>, n: int)
    requires s.len() > 0,
             1 <= n <= s.len()
    ensures seq_min(s.take(n)) == seq_min(s.take(n - 1)) || seq_min(s.take(n)) == s[n - 1]
    decreases n
{
    if n == 1 {
        assert(s.take(1) == seq![s[0]]);
        assert(seq_min(s.take(1)) == s[0]);
        assert(seq_min(s.take(0)).len() == 0);
    } else {
        let take_n = s.take(n);
        let take_n_minus_1 = s.take(n - 1);
        assert(take_n == take_n_minus_1.push(s[n - 1]));
        
        if take_n_minus_1.len() == 1 {
            assert(seq_min(take_n_minus_1) == take_n_minus_1[0]);
            if take_n_minus_1[0] <= s[n - 1] {
                assert(seq_min(take_n) == take_n_minus_1[0]);
                assert(seq_min(take_n) == seq_min(take_n_minus_1));
            } else {
                assert(seq_min(take_n) == s[n - 1]);
            }
        } else {
            let take_n_tail = seq_min(take_n.drop_first());
            if take_n[0] <= take_n_tail {
                assert(seq_min(take_n) == take_n[0]);
            } else {
                assert(seq_min(take_n) == take_n_tail);
            }
        }
    }
}

proof fn lemma_seq_max_take(s: Seq<int>, n: int)
    requires s.len() > 0,
             1 <= n <= s.len()
    ensures seq_max(s.take(n)) == seq_max(s.take(n - 1)) || seq_max(s.take(n)) == s[n - 1]
    decreases n
{
    if n == 1 {
        assert(s.take(1) == seq![s[0]]);
        assert(seq_max(s.take(1)) == s[0]);
        assert(seq_max(s.take(0)).len() == 0);
    } else {
        let take_n = s.take(n);
        let take_n_minus_1 = s.take(n - 1);
        assert(take_n == take_n_minus_1.push(s[n - 1]));
        
        if take_n_minus_1.len() == 1 {
            assert(seq_max(take_n_minus_1) == take_n_minus_1[0]);
            if take_n_minus_1[0] >= s[n - 1] {
                assert(seq_max(take_n) == take_n_minus_1[0]);
                assert(seq_max(take_n) == seq_max(take_n_minus_1));
            } else {
                assert(seq_max(take_n) == s[n - 1]);
            }
        } else {
            let take_n_tail = seq_max(take_n.drop_first());
            if take_n[0] >= take_n_tail {
                assert(seq_max(take_n) == take_n[0]);
            } else {
                assert(seq_max(take_n) == take_n_tail);
            }
        }
    }
}

fn compute_row_min(row: &Vec<i8>) -> (result: i8)
    requires row@.len() > 0
    ensures result as int == seq_min(row@.map(|j: int, x: i8| x as int))
{
    let mut min_val = row[0];
    let mut i = 1;
    
    while i < row.len()
        invariant
            0 < i <= row.len(),
            min_val as int == seq_min(row@.map(|j: int, x: i8| x as int).take(i as int)),
        decreases row.len() - i
    {
        if row[i] < min_val {
            min_val = row[i];
        }
        
        proof {
            let mapped_row = row@.map(|j: int, x: i8| x as int);
            lemma_seq_min_take(mapped_row, (i + 1) as int);
            
            let current_min = seq_min(mapped_row.take(i as int));
            let new_element = mapped_row[i as int];
            
            if current_min <= new_element {
                assert(seq_min(mapped_row.take((i + 1) as int)) == current_min);
            } else {
                assert(seq_min(mapped_row.take((i + 1) as int)) == new_element);
            }
        }
        
        i += 1;
    }
    
    min_val
}
// </vc-helpers>

// <vc-spec>
fn solve(grid: Vec<Vec<i8>>) -> (result: i8)
    requires valid_grid(grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
    ensures ({
        let grid_spec = grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));
        let row_mins = Seq::new(grid_spec.len(), |i: int| seq_min(grid_spec[i]));
        result as int == seq_max(row_mins)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed precondition validation and invariant maintenance */
    let mut row_mins: Vec<i8> = Vec::new();
    let mut i = 0;
    
    proof {
        let grid_spec = grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));
        assert(valid_grid(grid_spec));
        assert(forall|k: int| 0 <= k < grid.len() ==> grid@[k].len() > 0);
    }
    
    while i < grid.len()
        invariant
            0 <= i <= grid.len(),
            row_mins.len() == i,
            forall|k: int| 0 <= k < i ==> row_mins@[k] as int == seq_min(grid@[k]@.map(|j: int, x: i8| x as int)),
            forall|k: int| 0 <= k < grid.len() ==> grid@[k].len() > 0,
        decreases grid.len() - i
    {
        proof {
            assert(grid@[i as int].len() > 0);
        }
        let row_min = compute_row_min(&grid[i]);
        row_mins.push(row_min);
        i += 1;
    }
    
    let mut max_val = row_mins[0];
    let mut j = 1;
    
    while j < row_mins.len()
        invariant
            0 < j <= row_mins.len(),
            max_val as int == seq_max(row_mins@.map(|k: int, x: i8| x as int).take(j as int)),
        decreases row_mins.len() - j
    {
        if row_mins[j] > max_val {
            max_val = row_mins[j];
        }
        
        proof {
            let mapped_mins = row_mins@.map(|k: int, x: i8| x as int);
            lemma_seq_max_take(mapped_mins, (j + 1) as int);
            
            let current_max = seq_max(mapped_mins.take(j as int));
            let new_element = mapped_mins[j as int];
            
            if current_max >= new_element {
                assert(seq_max(mapped_mins.take((j + 1) as int)) == current_max);
            } else {
                assert(seq_max(mapped_mins.take((j + 1) as int)) == new_element);
            }
        }
        
        j += 1;
    }
    
    proof {
        let grid_spec = grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));
        let spec_row_mins = Seq::new(grid_spec.len(), |i: int| seq_min(grid_spec[i]));
        
        assert(row_mins@.len() == grid.len());
        assert(grid_spec.len() == grid.len());
        assert(spec_row_mins.len() == grid.len());
        
        assert(forall|k: int| 0 <= k < row_mins@.len() ==> 
            row_mins@[k] as int == seq_min(grid@[k]@.map(|j: int, x: i8| x as int)));
        
        assert(forall|k: int| 0 <= k < spec_row_mins.len() ==> 
            spec_row_mins[k] == seq_min(grid_spec[k]));
        
        assert(forall|k: int| 0 <= k < row_mins@.len() ==> 
            row_mins@[k] as int == spec_row_mins[k]);
        
        assert(row_mins@.map(|k: int, x: i8| x as int) =~= spec_row_mins);
        assert(max_val as int == seq_max(row_mins@.map(|k: int, x: i8| x as int)));
        assert(max_val as int == seq_max(spec_row_mins));
    }
    
    max_val
}
// </vc-code>


}

fn main() {}