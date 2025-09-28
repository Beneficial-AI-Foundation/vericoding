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
/* helper modified by LLM (iteration 5): no changes to helpers, compilation error is in code section */\n/* helper modified by LLM (iteration 4): fixed length specs to use @.len(), added new spec function for counting elements that equal x */\nspec fn less_i32(a: (i32, i32), b: (i32, i32)) -> bool {\n    let (x, y) = a;\n    let (u, v) = b;\n    x < u || (x == u && y > v)\n}\nspec fn less_eq_i32(a: (i32, i32), b: (i32, i32)) -> bool {\n    let (x, y) = a;\n    let (u, v) = b;\n    (x == u && y == v) || less_i32(a, b)\n}\nspec fn cmp_lt(a: (i32, i32), b: (i32, i32)) -> bool {\n    let (x, y) = a;\n    let (u, v) = b;\n    x < u || (x == u && y > v)\n}\nfn insert(pos: Vec<(i32, i32)>, item: (i32, i32)) -> (res: Vec<(i32, i32)>)\n    requires\n        (forall|j: int, k: int| 0 <= j < k < pos@.len() ==> #[trigger] less_eq_i32(pos@[j], pos@[k])),\n    ensures\n        res@.len() == pos@.len() + 1,\n        (forall|i: int| 0 <= i < res@.len() ==> {\n            (exists|k: int| 0 <= k < pos@.len() + 1 && (k < pos@.len() ==> res@[i] == pos@[k]) && (k == pos@.len() ==> res@[i] == item))\n        }),\n        (forall|i: int, j: int| 0 <= i < j < res@.len() ==> #[trigger] less_eq_i32(res@[i], res@[j])),\n        (forall|i: int| 0 <= i < res@.len() ==> #[trigger] pos@.contains(res@[i]))\n{\n    let mut i: usize = 0;\n    let mut res = pos;\n    while i < res.len()\n        invariant\n            0 <= i <= res@.len(),\n            res@.len() == pos@.len(),\n            (forall|j: int| 0 <= j < i ==> #[trigger] cmp_lt(res@[j], item)),\n            (forall|j: int| i <= j < res@.len() ==> #[trigger] cmp_lt(res@[j], item)),\n            (forall|j: int, k: int| 0 <= j < k < res@.len() && (j >= i || k < i) ==> #[trigger] less_eq_i32(res@[j], res@[k]))\n        decreases res.len() - i\n    {\n        if cmp_lt(res[i], item) {\n            i += 1;\n        } else {\n            res.insert(i, item);\n            return res;\n        }\n    }\n    res.push(item);\n    return res;\n}\nfn sort_positions(pos: Vec<(i32, i32)>) -> (res: Vec<(i32, i32)>)\n    ensures\n        res@.len() == pos@.len(),\n        (forall|i: int| 0 <= i < res@.len() ==> #[trigger] pos@.contains(res@[i])),\n        (forall|i: int| 0 <= i < pos@.len() ==> #[trigger] res@.contains(pos@[i])),\n        (forall|i: int, j: int| 0 <= i < j < res@.len() ==> #[trigger] less_eq_i32(res@[i], res@[j]))\n    decreases pos@.len()\n{\n    let mut res = Vec::new();\n    let mut i: usize = 0;\n    while i < pos.len()\n        invariant\n            res@.len() == i,\n            0 <= i <= pos@.len(),\n            (forall|j: int| 0 <= j < res@.len() ==> #[trigger] pos@.contains(res@[j])),\n            (forall|j: int| 0 <= j < res@.len() ==> #[trigger] res@.contains(res@[j])),\n            (forall|j: int, k: int| 0 <= j < k < res@.len() ==> #[trigger] less_eq_i32(res@[j], res@[k]))\n        decreases pos@.len() - i\n    {\n        res = insert(res, pos[i]);\n        i += 1;\n    }\n    return res;\n}
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
/* code modified by LLM (iteration 5): fixed sequence indexing in invariants by using @ for nested accesses to compile correctly */\n{\n    let mut positions: Vec<(i32, i32)> = Vec::new();\n    let lst_view = lst@;\n    let mut i: usize = 0;\n    while i < lst.len()\n        invariant\n            0 <= i <= lst@.len(),\n            positions@.len() == i,\n            (forall|j: int| 0 <= j < positions@.len() ==> {\n                let (a, b) = positions@[j];\n                0 <= a as int < lst_view.len() && 0 <= b as int < lst_view@[a as int].len() && lst_view@[a as int]@[b as int] as int == x as int\n            })\n        decreases lst.len() - i\n    {\n        let row = &lst[i];\n        let row_len = row.len();\n        let mut j: usize = 0;\n        while j < row_len\n            invariant\n                0 <= j <= row_len,\n                positions@.len() == i + j,\n                (forall|k: int| 0 <= k < positions@.len() ==> {\n                    let (a, b) = positions@[k];\n                    0 <= a as int < lst_view.len() && 0 <= b as int < lst_view@[a as int].len() && lst_view@[a as int]@[b as int] as int == x as int\n                })\n            decreases row_len - j\n        {\n            if row[j] == x {\n                positions.push((i as i32, j as i32));\n            }\n            j += 1;\n        }\n        i += 1;\n    }\n    \n    let sorted = sort_positions(positions);\n    let seq: Seq<(int, int)> = vstd::seq_lib::seq_map(sorted@, |p:(i32, i32)| (p.0 as int, p.1 as int));\n    return seq;\n}
// </vc-code>


}

fn main() {}