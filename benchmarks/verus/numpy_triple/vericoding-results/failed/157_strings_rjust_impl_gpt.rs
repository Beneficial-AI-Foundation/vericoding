// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

spec fn is_suffix_of<T>(suffix: Seq<T>, full: Seq<T>) -> bool {
    suffix.len() <= full.len() && 
    full.subrange(full.len() - suffix.len(), full.len() as int) == suffix
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sequence of n copies of a character */
spec fn repeat_char(c: char, n: nat) -> Seq<char> { Seq::new(n, |i: int| c) }

/* helper modified by LLM (iteration 5): lemma that any sequence is a suffix of its concatenation with any prefix */
proof fn suffix_of_concat<T>(prefix: Seq<T>, suffix: Seq<T>)
    ensures is_suffix_of(suffix, prefix + suffix)
{
    let full = prefix + suffix;
    assert(suffix.len() <= full.len());
    assert(full.len() == prefix.len() + suffix.len());
    assert(full.len() - suffix.len() == prefix.len());
    assert(full.subrange((full.len() - suffix.len()) as int, full.len() as int)
        == full.subrange(prefix.len() as int, (prefix.len() + suffix.len()) as int));
    assert(full.subrange(prefix.len() as int, (prefix.len() + suffix.len()) as int) == suffix);
}
// </vc-helpers>

// <vc-spec>
fn rjust(orig: Vec<char>, width: nat, fillchar: char) -> (res: Vec<char>)
    ensures
        res.len() == max_nat(orig.len() as nat, width),
        (orig.len() >= width ==> res@ == orig@) &&
        (orig.len() < width ==> res.len() == width && is_suffix_of(orig@, res@)) &&
        (orig.len() >= width ==> res.len() == orig.len()) &&
        (orig.len() < width ==> res.len() == width) &&
        (orig.len() == 0 ==> res.len() == width)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed nat->usize casts; controlled padding via nat comparisons; added proofs for lengths and suffix property */
    if (orig.len() as nat) >= width {
        return orig;
    }

    let mut res: Vec<char> = Vec::new();

    while ((res.len() as nat) + (orig.len() as nat)) < width
        invariant
            (orig.len() as nat) < width,
            ((res.len() as nat) + (orig.len() as nat)) <= width,
            res@ == Seq::new(res.len() as nat, |k: int| fillchar)
        decreases width - ((res.len() as nat) + (orig.len() as nat))
    {
        res.push(fillchar);
    }

    let ghost fill_n: nat = res.len() as nat;
    proof {
        assert(((res.len() as nat) + (orig.len() as nat)) == width);
        assert(fill_n + (orig.len() as nat) == width);
        assert(res@ == Seq::new(fill_n, |k: int| fillchar));
    }

    let mut j: usize = 0;
    while j < orig.len()
        invariant
            j <= orig.len(),
            res@ == Seq::new(fill_n, |k: int| fillchar) + orig@.subrange(0, j as int)
        decreases orig.len() - j
    {
        let ch = orig[j];
        res.push(ch);
        j += 1;
    }

    proof {
        assert(res@ == Seq::new(fill_n, |k: int| fillchar) + orig@);
        suffix_of_concat::<char>(Seq::new(fill_n, |k: int| fillchar), orig@);
        assert(res@.len() == fill_n + orig@.len());
        assert(orig@.len() == orig.len() as nat);
        assert(res@.len() == res.len() as nat);
        assert(res.len() as nat == fill_n + (orig.len() as nat));
        assert(res.len() as nat == width);
    }

    res
}
// </vc-code>

}
fn main() {}