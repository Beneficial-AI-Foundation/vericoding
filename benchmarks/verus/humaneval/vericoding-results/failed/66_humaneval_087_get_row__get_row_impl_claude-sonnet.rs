// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved int casting to spec functions only */
spec fn sorted_by_less_eq(s: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> less_eq(s[i], s[j])
}

proof fn lemma_insert_maintains_order(s: Seq<(int, int)>, elem: (int, int), pos: int)
    requires
        sorted_by_less_eq(s),
        0 <= pos <= s.len(),
        forall|i: int| 0 <= i < pos ==> less_eq(s[i], elem),
        forall|i: int| pos <= i < s.len() ==> less_eq(elem, s[i])
    ensures
        sorted_by_less_eq(s.insert(pos, elem))
{
}

spec fn map_to_int(positions: Seq<(i32, i32)>) -> Seq<(int, int)> {
    positions.map(|i, pair: (i32, i32)| (pair.0 as int, pair.1 as int))
}

fn find_insert_position(positions: &Vec<(i32, i32)>, elem: (i32, i32)) -> (pos: usize)
    requires
        sorted_by_less_eq(map_to_int(positions@)),
        forall|i: int| 0 <= i < positions@.len() ==> positions@[i].0 >= 0 && positions@[i].1 >= 0
    ensures
        pos <= positions@.len(),
        forall|i: int| 0 <= i < pos ==> less_eq((positions@[i].0 as int, positions@[i].1 as int), (elem.0 as int, elem.1 as int)),
        forall|i: int| pos <= i < positions@.len() ==> less_eq((elem.0 as int, elem.1 as int), (positions@[i].0 as int, positions@[i].1 as int))
{
    let mut idx = 0;
    while idx < positions.len()
        invariant
            0 <= idx <= positions@.len(),
            sorted_by_less_eq(map_to_int(positions@)),
            forall|i: int| 0 <= i < idx ==> less_eq((positions@[i].0 as int, positions@[i].1 as int), (elem.0 as int, elem.1 as int))
    {
        if elem.0 < positions[idx].0 || (elem.0 == positions[idx].0 && elem.1 > positions[idx].1) {
            return idx;
        }
        idx += 1;
    }
    idx
}
// </vc-helpers>

// <vc-spec>
fn get_row(lst: &Vec<Vec<i8>>, x: i8) -> (pos: SortSeqState)
    ensures 
        (forall|i: int| 0 <= i < pos.len() ==> #[trigger] pos[i].0 >= 0 && #[trigger] pos[i].1 >= 0 && {
            let (a, b) = pos[i];
            0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
        }) &&
        (forall|i: int, j: int| 0 <= i < lst@.len() && 0 <= j < lst@[i].len() && lst@[i][j] as int == x as int ==> #[trigger] pos.contains((i, j))) &&
        (forall|i: int, j: int| 0 <= i < j < pos.len() ==> #[trigger] less_eq(pos[i], pos[j]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variable for final mapping */
    let mut positions: Vec<(i32, i32)> = Vec::new();
    
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst@.len(),
            sorted_by_less_eq(map_to_int(positions@)),
            forall|k: int| 0 <= k < positions@.len() ==> positions@[k].0 >= 0 && positions@[k].1 >= 0 && {
                let (a, b) = (positions@[k].0 as int, positions@[k].1 as int);
                0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
            },
            forall|a: int, b: int| 0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> map_to_int(positions@).contains((a, b))
    {
        let mut j = 0;
        while j < lst[i].len()
            invariant
                0 <= i < lst@.len(),
                0 <= j <= lst@[i].len(),
                sorted_by_less_eq(map_to_int(positions@)),
                forall|k: int| 0 <= k < positions@.len() ==> positions@[k].0 >= 0 && positions@[k].1 >= 0 && {
                    let (a, b) = (positions@[k].0 as int, positions@[k].1 as int);
                    0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
                },
                forall|a: int, b: int| 0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> map_to_int(positions@).contains((a, b)),
                forall|b: int| 0 <= b < j && lst@[i][b] as int == x as int ==> map_to_int(positions@).contains((i, b))
        {
            if lst[i][j] == x {
                let elem = (i as i32, j as i32);
                let insert_pos = find_insert_position(&positions, elem);
                proof {
                    let ghost elem_ghost = (elem.0 as int, elem.1 as int);
                    lemma_insert_maintains_order(map_to_int(positions@), elem_ghost, insert_pos as int);
                }
                positions.insert(insert_pos, elem);
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        let ghost result = map_to_int(positions@);
        assert(result == map_to_int(positions@));
    }
    
    let ghost result = map_to_int(positions@);
    result
}
// </vc-code>


}

fn main() {}