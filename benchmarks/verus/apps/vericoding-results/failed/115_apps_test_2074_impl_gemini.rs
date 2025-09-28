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
proof fn lemma_min_ge_than_all(s: Seq<int>, lower_bound: int)
    requires
        s.len() > 0,
        forall|j: int| 0 <= j < s.len() ==> lower_bound <= s[j],
    ensures
        lower_bound <= seq_min(s),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_min_ge_than_all(s.drop_first(), lower_bound);
    }
}

proof fn lemma_min_value_is_seq_min(s: Seq<int>, min_val: int)
    requires
        s.len() > 0,
        exists|k: int| 0 <= k < s.len() && min_val == s[k],
        forall|j: int| 0 <= j < s.len() ==> min_val <= s[j],
    ensures
        min_val == seq_min(s),
    decreases s.len(),
{
    if s.len() > 1 {
        let tail = s.drop_first();
        let k = choose|k: int| 0 <= k < s.len() && min_val == s[k];
        if k == 0 {
            lemma_min_ge_than_all(tail, min_val);
        } else {
            assert(exists|kt: int| 0 <= kt < tail.len() && min_val == tail[kt]);
            lemma_min_value_is_seq_min(tail, min_val);
        }
    }
}

fn find_row_min(row: &Vec<i8>) -> (min_val: i8)
    requires
        row.len() > 0,
    ensures
        min_val as int == seq_min(row@.map(|_idx, x: i8| x as int)),
{
    let mut min = row[0];
    let mut i: usize = 1;
    while i < row.len()
        invariant
            row.len() > 0,
            1 <= i <= row.len(),
            exists|k: int| 0 <= k < (i as int) && min == row@[k],
            forall|j: int| 0 <= j < (i as int) ==> min <= row@[j],
        decreases row.len() - i,
    {
        if *row.index(i) < min {
            min = *row.index(i);
        }
        i = i + 1;
    }
    proof {
        let s = row@.map(|_idx, x: i8| x as int);
        assert(exists|k: int| 0 <= k < s.len() && min as int == s[k]);
        assert(forall|j: int| 0 <= j < s.len() ==> min as int <= s[j]);
        lemma_min_value_is_seq_min(s, min as int);
    }
    min
}

proof fn lemma_max_le_than_all(s: Seq<int>, upper_bound: int)
    requires
        s.len() > 0,
        forall|j: int| 0 <= j < s.len() ==> upper_bound >= s[j],
    ensures
        upper_bound >= seq_max(s),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_max_le_than_all(s.drop_first(), upper_bound);
    }
}

proof fn lemma_max_value_is_seq_max(s: Seq<int>, max_val: int)
    requires
        s.len() > 0,
        exists|k: int| 0 <= k < s.len() && max_val == s[k],
        forall|j: int| 0 <= j < s.len() ==> max_val >= s[j],
    ensures
        max_val == seq_max(s),
    decreases s.len(),
{
    if s.len() > 1 {
        let tail = s.drop_first();
        let k = choose|k: int| 0 <= k < s.len() && max_val == s[k];
        if k == 0 {
            lemma_max_le_than_all(tail, max_val);
        } else {
            assert(exists|kt: int| 0 <= kt < tail.len() && max_val == tail[kt]);
            lemma_max_value_is_seq_max(tail, max_val);
        }
    }
}

fn find_vec_max(vals: &Vec<i8>) -> (max_val: i8)
    requires
        vals.len() > 0,
    ensures
        max_val as int == seq_max(vals@.map(|_idx, x: i8| x as int)),
{
    let mut max = vals[0];
    let mut i: usize = 1;
    while i < vals.len()
        invariant
            vals.len() > 0,
            1 <= i <= vals.len(),
            exists|k: int| 0 <= k < (i as int) && max == vals@[k],
            forall|j: int| 0 <= j < (i as int) ==> max >= vals@[j],
        decreases vals.len() - i,
    {
        if *vals.index(i) > max {
            max = *vals.index(i);
        }
        i = i + 1;
    }
    proof {
        let s = vals@.map(|_idx, x: i8| x as int);
        assert(exists|k: int| 0 <= k < s.len() && max as int == s[k]);
        assert(forall|j: int| 0 <= j < s.len() ==> max as int >= s[j]);
        lemma_max_value_is_seq_max(s, max as int);
    }
    max
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
    /* code modified by LLM (iteration 3): fixed compilation error `ghost let` syntax and proof structure */
    let mut row_mins_vec: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    let ghost grid_spec = grid@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int));

    while i < grid.len()
        invariant
            grid.len() > 0,
            0 <= i <= grid.len(),
            row_mins_vec.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> 
                row_mins_vec@[j] as int == seq_min(grid_spec[j]),
        decreases grid.len() - i,
    {
        let row_min = find_row_min(grid.index(i));
        row_mins_vec.push(row_min);
        i = i + 1;
    }

    assert(grid.len() > 0 ==> row_mins_vec.len() > 0);
    let final_max = find_vec_max(&row_mins_vec);

    proof {
        let row_mins_from_impl = row_mins_vec@.map(|_idx, x: i8| x as int);
        let row_mins_from_spec = Seq::new(grid_spec.len(), |i: int| seq_min(grid_spec[i]));
        
        assert forall|j: int| 0 <= j < grid.len() implies
            row_mins_from_impl[j] == row_mins_from_spec[j];
        
        assert(row_mins_from_impl =~= row_mins_from_spec);

        assert(final_max as int == seq_max(row_mins_from_impl));
        assert(seq_max(row_mins_from_impl) == seq_max(row_mins_from_spec));
    }

    final_max
}
// </vc-code>


}

fn main() {}