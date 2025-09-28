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
/* helper modified by LLM (iteration 5): noop helper kept for placeholder */
proof fn helpers_noop() { }
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
    /* code modified by LLM (iteration 5): build spec sequence of positions using proof-only loops; replace Seq::unit with Seq::new on a temporary Vec */
    let mut res: Seq<(int, int)>;
    proof {
        res = Seq::empty();
        let mut i: int = 0;
        while i < lst@.len()
            invariant
                0 <= i && i <= lst@.len(),
                (forall|a: int, b: int| 0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> res.contains((a, b))),
                (forall|u: int, v: int| 0 <= u < v < res.len() ==> less_eq(res[u], res[v])),
            decreases lst@.len() - i
        {
            let mut j: int = 0;
            while j < lst@[i].len()
                invariant
                    0 <= j && j <= lst@[i].len(),
                    (forall|a: int, b: int| ((0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int) || (a == i && 0 <= b < j && lst@[a][b] as int == x as int)) ==> res.contains((a, b))),
                    (forall|u: int, v: int| 0 <= u < v < res.len() ==> less_eq(res[u], res[v])),
                decreases lst@[i].len() - j
            {
                if lst@[i][j] as int == x as int {
                    let mut tmp: Vec<(int, int)> = Vec::new();
                    tmp.push((i, j));
                    res = res + Seq::new(tmp);
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }
    res
}
// </vc-code>


}

fn main() {}