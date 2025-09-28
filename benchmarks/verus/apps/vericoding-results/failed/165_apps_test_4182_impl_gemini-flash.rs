// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool {
    xx.len() == n && yy.len() == m && n >= 1 && m >= 1 && x < y
}

spec fn agreement_possible(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool 
    recommends valid_input(n, m, x, y, xx, yy)
{
    let combined_x = xx.push(x);
    let combined_y = yy.push(y);
    exists|max_val: int| combined_x.contains(max_val) && 
                         (forall|v: int| combined_x.contains(v) ==> v <= max_val) &&
    exists|min_val: int| combined_y.contains(min_val) && 
                         (forall|v: int| combined_y.contains(v) ==> v >= min_val) &&
                         max_val < min_val
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Simplified `lemma_max_min_of_sequences` to directly retrieve the maximum and minimum elements using an iterator-like approach and then assert the existence and properties of these values in the sequences. Removed unnecessary loop invariants. */
proof fn lemma_max_min_of_sequences(s1: Seq<int>, s2: Seq<int>)
    requires
        s1.len() > 0,
        s2.len() > 0,
    ensures
        exists|max_val: int| s1.contains(max_val) && (forall|v: int| s1.contains(v) ==> v <= max_val),
        exists|min_val: int| s2.contains(min_val) && (forall|v: int| s2.contains(v) ==> v >= min_val),
{
    let mut current_max = s1[0];
    let mut i: nat = 1;
    while i < s1.len()
        invariant
            0 < s1.len(),
            0 <= i && i <= s1.len(),
            s1.contains(current_max),
            forall|k: nat| 0 <= k < i ==> s1[k] <= current_max,
        decreases s1.len() - i
    {
        if s1[i] > current_max {
            current_max = s1[i];
        }
        i = (i + 1) as nat;
    }

    assert(s1.contains(current_max));
    assert(forall|v: int| s1.contains(v) ==> v <= current_max);

    let mut current_min = s2[0];
    let mut j: nat = 1;
    while j < s2.len()
        invariant
            0 < s2.len(),
            0 <= j && j <= s2.len(),
            s2.contains(current_min),
            forall|k: nat| 0 <= k < j ==> s2[k] >= current_min,
        decreases s2.len() - j
    {
        if s2[j] < current_min {
            current_min = s2[j];
        }
        j = (j + 1) as nat;
    }

    assert(s2.contains(current_min));
    assert(forall|v: int| s2.contains(v) ==> v >= current_min);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, x: i8, y: i8, xx: Vec<i8>, yy: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)),
    ensures 
        result@ == seq!['N','o',' ','W','a','r'] || result@ == seq!['W','a','r'],
        (result@ == seq!['N','o',' ','W','a','r']) == agreement_possible(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Ensured that all `int` type casts are performed only within `ghost` contexts to resolve compilation errors. Corrected loop invariants to align with the values being found within the `i8` vectors. */
{
    let ghost n_int = n as int;
    let ghost m_int = m as int;
    let ghost x_int = x as int;
    let ghost y_int = y as int;

    let ghost xx_ghost = xx@.map_values(|v: i8| v as int);
    let ghost yy_ghost = yy@.map_values(|v: i8| v as int);

    let ghost combined_x_seq = xx_ghost.push(x_int);
    let ghost combined_y_seq = yy_ghost.push(y_int);

    proof {
        lemma_max_min_of_sequences(combined_x_seq, combined_y_seq);
    }

    let mut max_val: i8 = xx[0];
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i && i <= n as usize,
            forall|k: nat| 0 <= (k as usize) < i ==> xx[k as usize] <= max_val,
            exists|k: nat| 0 <= (k as usize) < i ==> xx[k as usize] == max_val,
        decreases (n as usize) - i
    {
        if xx[i] > max_val {
            max_val = xx[i];
        }
        i = i + 1;
    }

    // Include x in max_val check
    if x > max_val {
        max_val = x;
    }

    let mut min_val: i8 = yy[0];
    let mut j: usize = 0;
    while j < m as usize
        invariant
            0 <= j && j <= m as usize,
            forall|k: nat| 0 <= (k as usize) < j ==> yy[k as usize] >= min_val,
            exists|k: nat| 0 <= (k as usize) < j ==> yy[k as usize] == min_val,
        decreases (m as usize) - j
    {
        if yy[j] < min_val {
            min_val = yy[j];
        }
        j = j + 1;
    }

    // Include y in min_val check
    if y < min_val {
        min_val = y;
    }

    if max_val < min_val {
        String::from("No War")
    } else {
        String::from("War")
    }
}
// </vc-code>


}

fn main() {}