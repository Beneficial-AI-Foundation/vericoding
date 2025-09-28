// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, p: Seq<int>) -> bool {
    p.len() == n && n >= 3
}

spec fn count_median_elements(p: Seq<int>, n: int) -> nat {
    if valid_input(n, p) {
        Set::new(|i: int| 0 <= i < n - 2 && is_median_of_three(p[i], p[i + 1], p[i + 2])).len()
    } else {
        0
    }
}

spec fn is_median_of_three(a: int, b: int, c: int) -> bool {
    (a < b && b < c) || (a > b && b > c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [retaining correct helper] */
fn check_median(a: i8, b: i8, c: i8) -> (res: bool)
    ensures
        res == is_median_of_three(a as int, b as int, c as int),
{
    (a < b && b < c) || (a > b && b > c)
}

/* helper modified by LLM (iteration 5): [added spec function for loop invariant] */
spec fn count_up_to(p: Seq<int>, i: int) -> nat {
    Set::new(|k: int| 0 <= k < i && is_median_of_three(p[k], p[k+1], p[k+2])).len()
}

/* helper modified by LLM (iteration 5): [added lemma for count_up_to] */
proof fn lemma_count_up_to_increment(p: Seq<int>, i: int)
    requires
        p.len() >= 3,
        0 <= i < p.len() - 2,
    ensures
        count_up_to(p, i + 1) == count_up_to(p, i) +
            (if is_median_of_three(p[i], p[i+1], p[i+2]) { 1 } else { 0 }),
{
    let s_prefix = Set::new(|k: int| 0 <= k < i && is_median_of_three(p[k], p[k+1], p[k+2]));
    let s_i = Set::new(|k: int| k == i && is_median_of_three(p[i], p[i+1], p[i+2]));
    let s_total = Set::new(|k: int| 0 <= k < i+1 && is_median_of_three(p[k], p[k+1], p[k+2]));
    
    assert(s_total =~= s_prefix.union(s_i)) by(ext_equal);
    assert(s_prefix.disjoint(s_i));
    vstd::set_lib::lemma_len_union_disjoint(s_prefix, s_i);

    if is_median_of_three(p[i], p[i+1], p[i+2]) {
        assert(s_i.len() == 1);
    } else {
        assert(s_i.len() == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, p: Vec<i8>) -> (result: u8)
    requires
        valid_input(n as int, p@.map(|i: int, x: i8| x as int)),
    ensures
        result <= n - 2,
        result as nat == count_median_elements(p@.map(|i: int, x: i8| x as int), n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [used helper spec function in invariant and called lemma] */
    let ghost p_int = p@.map(|_i: int, x: i8| x as int);
    let mut count: u8 = 0;
    let mut i: u8 = 0;
    while i < n - 2
        invariant
            p_int == p@.map(|_i: int, x: i8| x as int),
            valid_input(n as int, p_int),
            0 <= i <= n - 2,
            count <= i,
            count as nat == count_up_to(p_int, i as int),
        decreases n - 2 - i
    {
        proof {
            if i < n - 2 {
                lemma_count_up_to_increment(p_int, i as int);
            }
        }

        let a = p[i as usize];
        let b = p[(i + 1) as usize];
        let c = p[(i + 2) as usize];
        if check_median(a, b, c) {
            count = count + 1;
        }
        i = i + 1;
    }

    assert(count_up_to(p_int, (n - 2) as int) == count_median_elements(p_int, n as int));
    
    count
}
// </vc-code>


}

fn main() {}