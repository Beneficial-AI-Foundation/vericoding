use vstd::prelude::*;

verus! {

spec fn count<T>(s: Seq<T>, x: T) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.skip(1), x) + if s[0] == x {
            1int
        } else {
            0int
        }
    }
}
// pure-end
// pure-end

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end
// pure-end

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// pure-end

// <vc-helpers>
spec fn sorted_sequence(s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> s[i] <= s[i+1]
}

fn insertion_sort(v: Vec<i32>) -> (res: Vec<i32>)
    ensures permutes(res@, v@),
    ensures sorted_sequence(res@)
{
    let mut res = Vec::new();
    for i in 0..v.len() {
        invariant {
            let prefix = v@.prefix(i);
            permutes(res@, prefix) && sorted_sequence(res@)
        }
        let x = v[i];
        let mut j = res.len();
        invariant {
            sorted_sequence(res@.prefix(j)) &&
            (j == res.len() || x <= res[j])
        }
        while j > 0 && res[j-1] > x {
            res.insert(j, res[j-1]);
            j = j - 1;
        }
        res.insert(j, x);
    }
    res
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut evens = Vec::new();
    for i in 0..l.len() {
        if i % 2 == 0 {
            evens.push(l[i]);
        }
    }
    evens = insertion_sort(evens);
    let mut res = Vec::new();
    let mut evens_index = 0;
    for i in 0..l.len() {
        if i % 2 == 0 {
            res.push(evens[evens_index]);
            evens_index += 1;
        } else {
            res.push(l[i]);
        }
    }
    res
}
// </vc-code>

fn main() {}
}