// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
// </vc-spec>
// <vc-code>
{
    let n: usize = list.len();
    let mut arr = list;
    if n <= 1 {
        return arr;
    }
    let mut width: usize = 1;
    while width < n
    {
        let mut temp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
        {
            let l = i;
            let m = min_usize(i.saturating_add(width), n);
            let r = min_usize(m.saturating_add(width), n);

            let mut p = l;
            let mut q = m;
            while p < m && q < r
            {
                let vp = arr[p];
                let vq = arr[q];
                if vp <= vq {
                    temp.push(vp);
                    p = p + 1;
                } else {
                    temp.push(vq);
                    q = q + 1;
                }
            }
            while p < m
            {
                let vp = arr[p];
                temp.push(vp);
                p = p + 1;
            }
            while q < r
            {
                let vq = arr[q];
                temp.push(vq);
                q = q + 1;
            }
            i = r;
        }
        arr = temp;
        if width > n / 2 { break; }
        width = width * 2;
    }
    arr
}
// </vc-code>

}
fn main() {}