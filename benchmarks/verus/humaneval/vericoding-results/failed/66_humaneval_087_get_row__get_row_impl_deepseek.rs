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
/* helper modified by LLM (iteration 5): Fix type conversion and ensure proper insertion */
proof fn collect_positions(lst_view: Seq<Vec<i8>>, x: i8) -> (result: Seq<(int, int)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].0 >= 0 && #[trigger] result[i].1 >= 0 && {
            let (a, b) = result[i];
            0 <= a < lst_view.len() && 0 <= b < lst_view[a].len() && lst_view[a][b] as int == x as int
        },
        forall|i: int, j: int| 0 <= i < lst_view.len() && 0 <= j < lst_view[i].len() && lst_view[i][j] as int == x as int ==> #[trigger] result.contains((i, j)),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] less_eq(result[i], result[j])
{
    let mut result: Seq<(int, int)> = Seq::empty();
    let mut i: int = 0;
    
    while i < lst_view.len()
        invariant
            0 <= i <= lst_view.len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < lst_view[k].len() && lst_view[k][l] as int == x as int ==> 
                #[trigger] result.contains((k, l)),
            forall|p: int| 0 <= p < result.len() ==> {
                let (a, b) = result[p];
                0 <= a < i && 0 <= b < lst_view[a].len() && lst_view[a][b] as int == x as int
            },
            forall|p: int, q: int| 0 <= p < q < result.len() ==> less_eq(result[p], result[q])
        decreases lst_view.len() - i
    {
        let mut j: int = 0;
        
        while j < lst_view[i].len()
            invariant
                0 <= j <= lst_view[i].len(),
                forall|k: int| 0 <= k < j && lst_view[i][k] as int == x as int ==> #[trigger] result.contains((i, k)),
                forall|p: int| 0 <= p < result.len() ==> {
                    let (a, b) = result[p];
                    0 <= a < i || (a == i && 0 <= b < j)
                },
                forall|p: int, q: int| 0 <= p < q < result.len() ==> less_eq(result[p], result[q])
            decreases lst_view[i].len() - j
        {
            if lst_view[i][j] as int == x as int {
                result = result.insert(result.len() as int, (i, j));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 5): Use proof block and return collected positions */
    proof {
        let ghost_result = collect_positions(lst@, x);
        ghost_result
    }
}
// </vc-code>


}

fn main() {}