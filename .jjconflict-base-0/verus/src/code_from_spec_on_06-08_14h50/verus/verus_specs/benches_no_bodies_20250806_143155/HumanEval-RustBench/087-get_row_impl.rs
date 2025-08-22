use vstd::prelude::*;

verus! {

spec fn row_sorted_asc(coords: Seq<(usize, usize)>) -> (ret:bool) {
    forall|i: usize, j: usize|
        0 <= i < j < coords.len() ==> #[trigger] coords[i as int].0 <= #[trigger] coords[j as int].0
}
// pure-end

spec fn row_col_sorted_desc(coords: Seq<(usize, usize)>) -> (ret:bool) {
    forall|i: usize, j: usize|
        0 <= i < j < coords.len() && #[trigger] coords[i as int].0 == #[trigger] coords[j as int].0
            ==> coords[i as int].1 > coords[j as int].1
}
// pure-end

spec fn coords_complete_for_row_until_col(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
    row: usize,
    col: usize,
) -> (ret:bool)
    recommends
        0 <= row < lst.len(),
{
    forall|j: usize|
        #![trigger lst[row as int][j as int]]
        0 <= j < lst[row as int].len() && col <= j && lst[row as int][j as int] == x ==> exists|
            k: int,
        |
            0 <= k < coords.len() && #[trigger] coords[k] == (row, j)
}
// pure-end

spec fn coords_complete_until_row(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
    row: usize,
) -> (ret:bool) {
    forall|i: usize|
        #![trigger lst[i as int]]
        0 <= i < lst.len() && i < row ==> coords_complete_for_row_until_col(lst, x, coords, i, 0)
}
// pure-end

spec fn coords_complete(lst: Seq<Seq<i32>>, x: i32, coords: Seq<(usize, usize)>) -> (ret:bool) {
    coords_complete_until_row(lst, x, coords, lst.len() as usize)
}
// pure-end

spec fn coords_sound(lst: Seq<Seq<i32>>, x: i32, coords: Seq<(usize, usize)>) -> (ret:bool) {
    forall|i: usize, j: usize|
        #![trigger lst[i as int][j as int]]
        #![trigger coords.contains((i,j))]
        0 <= i < lst.len() && 0 <= j < lst[i as int].len() && coords.contains((i, j))
            ==> lst[i as int][j as int] == x
}
// pure-end

spec fn coords_distinct(coords: Seq<(usize, usize)>) -> (ret:bool) {
    forall|i: int, j: int| 0 <= i < j < coords.len() ==> coords[i] != coords[j]
}
// pure-end

spec fn coords_matches_lst(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
) -> (ret:bool) {
    &&& coords_complete(lst, x, coords)
    &&& coords_sound(lst, x, coords)
    &&& coords_distinct(coords)
}
// pure-end

proof fn coords_distinct_after_push(coords: Seq<(usize, usize)>, x: usize, y: usize)
    // pre-conditions-start
    requires
        coords_distinct(coords),
        forall|k: int|
            0 <= k < coords.len() ==> #[trigger] coords[k].0 < x || #[trigger] coords[k].1 > y,
    // pre-conditions-end
    // post-conditions-start
    ensures
        coords_distinct(coords.push((x, y))),
    // post-conditions-end
{
    // impl-start
    if (coords.len() > 0) {
        assert forall|i: int, j: int| 0 <= i < j < coords.push((x, y)).len() implies coords.push(
            (x, y),
        )[i] != coords.push((x, y))[j] by {
            if (j < coords.len()) {
            } else {
                assert(coords[i].0 != x || coords[i].1 > y);
            }
        }
    }
    // impl-end
}
// pure-end

fn get_row(lst: Vec<Vec<i32>>, x: i32) -> (coords: Vec<(usize, usize)>)
    // post-conditions-start
    ensures
        coords_matches_lst(lst.deep_view(), x, coords@),
        row_sorted_asc(coords@),
        row_col_sorted_desc(coords@),
    // post-conditions-end
{
    let mut coords = Vec::new();
    
    for row in 0..lst.len()
        invariant
            coords_matches_lst(lst.deep_view(), x, coords@),
            row_sorted_asc(coords@),
            row_col_sorted_desc(coords@),
            coords_complete_until_row(lst.deep_view(), x, coords@, row),
    {
        let mut row_coords: Vec<(usize, usize)> = Vec::new();
        
        for col in 0..lst[row].len()
            invariant
                forall|k: int| 0 <= k < row_coords.len() ==> row_coords@[k].0 == row,
                forall|k: int| 0 <= k < row_coords.len() ==> lst.deep_view()[row as int][row_coords@[k].1 as int] == x,
                forall|i: int, j: int| 0 <= i < j < row_coords.len() ==> row_coords@[i].1 > row_coords@[j].1,
                coords_complete_for_row_until_col(lst.deep_view(), x, row_coords@, row, col),
        {
            if lst[row][col] == x {
                row_coords.insert(0, (row, col));
            }
        }
        
        for coord_idx in 0..row_coords.len()
            invariant
                coords_matches_lst(lst.deep_view(), x, coords@),
                row_sorted_asc(coords@),
                row_col_sorted_desc(coords@),
                coords_complete_until_row(lst.deep_view(), x, coords@, row),
                /* code modified by LLM (iteration 1): Fixed trigger syntax to use #![trigger] instead of let variable in trigger */
                forall|k: int| coord_idx <= k < row_coords.len() ==> {
                    #![trigger row_coords@[k as int]]
                    #![trigger lst.deep_view()[row as int][row_coords@[k as int].1 as int]]
                    row_coords@[k as int].0 == row && lst.deep_view()[row as int][row_coords@[k as int].1 as int] == x
                },
                forall|k: int| 0 <= k < coord_idx ==> {
                    coords@.contains(row_coords@[k as int])
                },
                forall|k: int| 0 <= k < coords.len() ==> coords@[k].0 <= row,
        {
            let coord = row_coords[coord_idx];
            proof {
                /* code modified by LLM (iteration 1): Added proof block for distinctness property */
                coords_distinct_after_push(coords@, coord.0, coord.1);
            }
            coords.push(coord);
        }
    }
    
    coords
}

} // verus!
fn main() {}