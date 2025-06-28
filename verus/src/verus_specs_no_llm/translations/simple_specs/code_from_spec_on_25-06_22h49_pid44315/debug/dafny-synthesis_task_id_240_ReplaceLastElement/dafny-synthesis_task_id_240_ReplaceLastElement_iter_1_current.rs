Let me analyze the ensures clauses:
- Result length should be `first.len() - 1 + second.len()`
- First part of result should match `first` (except last element)
- Second part should match `second`

Here's the implementation:

// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceLastElement(first: Seq<int>, second: Seq<int>) -> (result: Seq<int>)
    requires
        first.len() > 0
    ensures
        result.len() == first.len() - 1 + second.len(),
        forall|i: int| 0 <= i < first.len() - 1 ==> result.spec_index(i) == first.spec_index(i),
        forall|i: int| first.len() - 1 <= i < result.len() ==> result.spec_index(i) == second.spec_index(i - first.len() + 1)
{
    let first_part = first.subrange(0, first.len() - 1);
    let result = first_part.add(second);
    result
}

}

The implementation: