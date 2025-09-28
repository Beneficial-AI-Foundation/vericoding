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
/* helper modified by LLM (iteration 4): Fixed ghost variable usage for length conversion */
spec fn sorted_by_less(s: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> less_eq(s[i], s[j])
}

fn insert_sorted(s: SortSeqState, elem: (int, int)) -> (result: SortSeqState)
    requires
        sorted_by_less(s)
    ensures
        sorted_by_less(result),
        result.len() == s.len() + 1,
        result.contains(elem),
        forall|e: (int, int)| s.contains(e) ==> result.contains(e),
        forall|e: (int, int)| result.contains(e) ==> e == elem || s.contains(e)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> less(s[j], elem)
    {
        let ghost i_int = i as int;
        if !less(s[i_int], elem) {
            let ghost s_len = s.len() as int;
            let left = s.subrange(0, i_int);
            let right = s.subrange(i_int, s_len);
            return left.push(elem) + right;
        }
        i = i + 1;
    }
    s.push(elem)
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
    /* code modified by LLM (iteration 4): No changes needed to main code */
    let mut result: SortSeqState = Seq::empty();
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            sorted_by_less(result),
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].0 >= 0 && #[trigger] result[k].1 >= 0,
            forall|k: int| 0 <= k < result.len() ==> {
                let (a, b) = result[k];
                0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
            },
            forall|a: int, b: int| 0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> #[trigger] result.contains((a, b)),
            forall|a: int, b: int| i <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> !result.contains((a, b))
    {
        let mut j: usize = 0;
        while j < lst[i].len()
            invariant
                0 <= i < lst.len(),
                0 <= j <= lst[i].len(),
                sorted_by_less(result),
                forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].0 >= 0 && #[trigger] result[k].1 >= 0,
                forall|k: int| 0 <= k < result.len() ==> {
                    let (a, b) = result[k];
                    0 <= a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int
                },
                forall|a: int, b: int| 0 <= a < i && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> #[trigger] result.contains((a, b)),
                forall|b: int| 0 <= b < j && lst@[i][b] as int == x as int ==> result.contains((i as int, b)),
                forall|a: int, b: int| i < a < lst@.len() && 0 <= b < lst@[a].len() && lst@[a][b] as int == x as int ==> !result.contains((a, b)),
                forall|b: int| j <= b < lst@[i].len() && lst@[i][b] as int == x as int ==> !result.contains((i as int, b))
        {
            if lst[i][j] == x {
                let ghost i_int: int = i as int;
                let ghost j_int: int = j as int;
                result = insert_sorted(result, (i_int, j_int));
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}