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
/* helper modified by LLM (iteration 5): fixed ensures clause to use v@ instead of v.push(elem)@ */
proof fn subrange_suffix_lemma<T>(s: Seq<T>, suffix: Seq<T>)
    requires suffix.len() <= s.len()
    ensures s.subrange(s.len() - suffix.len(), s.len() as int).len() == suffix.len()
{
}

proof fn vec_push_preserves_suffix<T>(v: Vec<T>, suffix: Seq<T>, elem: T)
    requires is_suffix_of(suffix, v@)
    ensures is_suffix_of(suffix, v@.push(elem))
{
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
    /* code modified by LLM (iteration 5): fixed nat usage in ghost variable */
    if orig.len() >= width {
        orig
    } else {
        let mut result = Vec::new();
        let ghost fill_count: nat = width - orig.len() as nat;
        
        for i in 0..width - orig.len()
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == fillchar
        {
            result.push(fillchar);
        }
        
        for i in 0..orig.len()
            invariant
                result.len() == (width - orig.len()) + i,
                forall|j: int| 0 <= j < width - orig.len() ==> result@[j] == fillchar,
                forall|j: int| 0 <= j < i ==> result@[(width - orig.len()) + j] == orig@[j]
        {
            result.push(orig[i]);
        }
        
        proof {
            assert(result.len() == width);
            assert(is_suffix_of(orig@, result@));
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}