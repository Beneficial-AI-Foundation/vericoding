use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn seq_zip_skip_lemma<A, B>(s1: Seq<A>, s2: Seq<B>) 
    requires
        s1.len() == s2.len(),
    ensures
        s1.skip(1).zip(s2.skip(1)) =~= s1.zip(s2).skip(1),
{
    if s1.len() > 0 {
        assert(s1.skip(1) =~= s1.subrange(1, s1.len() as int));
        assert(s2.skip(1) =~= s2.subrange(1, s2.len() as int));
        assert(s1.subrange(1, s1.len() as int).zip(s2.subrange(1, s2.len() as int)) =~= s1.zip(s2).subrange(1, s1.len() as int));
        assert(s1.zip(s2).skip(1) =~= s1.zip(s2).subrange(1, s1.len() as int));
        assert(s1.skip(1).zip(s2.skip(1)) =~= s1.zip(s2).skip(1));
    }
}

proof fn seq_map_values_lemma<A, B, C>(s: Seq<A>, f: FnSpec(int, A) -> B, g: FnSpec(int, B) -> C) 
    ensures
        s.map(f).map(g) =~= s.map(|i, x| g(i, f(i, x))),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s.map(f)[i] == f(i, s[i]) by { };
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s.map(f).map(g)[i] == g(i, f(i, s[i])) by { };
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s.map(|idx, x| g(idx, f(idx, x)))[i] == g(i, f(i, s[i])) by { };
}

proof fn derivative_post_lemma(xs: Seq<int>, ret: Seq<int>) 
    requires
        xs.len() > 0,
        ret.len() == xs.len() - 1,
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == (i + 1) * xs[i + 1],
    ensures
        xs.map(|i: int, x| i * x).skip(1) =~= ret,
{
    let left = xs.map(|i: int, x| i * x).skip(1);
    let right = ret;
    
    assert(left.len() == xs.len() - 1);
    assert(right.len() == xs.len() - 1);
    
    let n = left.len() as int;
    proof {
        let mut j: int = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|k: int| 0 <= k < j ==> left[k] == right[k],
        {
            assert(left[j] == (j + 1) * xs[j + 1]);
            assert(right[j] == (j + 1) * xs[j + 1]);
            j = j + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if xs.is_empty() {
        Some(Vec::new())
    } else {
        let mut result = Vec::with_capacity(xs.len() - 1);
        let mut i: usize = 0;
        while i < xs.len() - 1
            invariant
                0 <= i <= xs@.len() - 1,
                result@.len() == i as nat,
                forall|j: int| 0 <= j < i as int ==> result@[j] as int == (j + 1) * xs@[j + 1],
        {
            let val = (i + 1) * xs[i + 1];
            result.push(val);
            i = i + 1;
        }
        Some(result)
    }
}
// </vc-code>

fn main() {}
}