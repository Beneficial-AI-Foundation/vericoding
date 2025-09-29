// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_subrange_push<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len()
    ensures
        s.subrange(0, i).push(s[i]) == s.subrange(0, i + 1)
{ }

proof fn lemma_add_push_left<T>(a: Seq<T>, b: Seq<T>, x: T)
    ensures
        (a.add(b)).push(x) == a.add(b.push(x))
{ }
// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)

    requires
        first.len() > 0,

    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
// </vc-spec>
// <vc-code>
{
    let n1 = first.len();
    let n2 = second.len();
    let mut res: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n1 - 1
        invariant
            n1 == first.len(),
            0 <= i as int,
            i <= n1 - 1,
            res@ == first@.subrange(0, i as int),
        decreases (n1 - 1 - i) as int
    {
        proof {
            lemma_subrange_push::<i32>(first@, i as int);
        }
        res.push(first[i]);
        i += 1;
    }

    let mut j: usize = 0;
    while j < n2
        invariant
            n1 == first.len(),
            n2 == second.len(),
            0 <= j as int,
            j <= n2,
            res@ == first@.subrange(0, n1 as int - 1).add(second@.subrange(0, j as int)),
        decreases (n2 - j) as int
    {
        proof {
            lemma_add_push_left::<i32>(first@.subrange(0, n1 as int - 1), second@.subrange(0, j as int), second@[j as int]);
            lemma_subrange_push::<i32>(second@, j as int);
        }
        res.push(second[j]);
        j += 1;
    }

    res
}
// </vc-code>

}
fn main() {}