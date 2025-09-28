// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix predicate syntax by adding ! */
predicate contains(s: Seq<i8>, elem: i8) {
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

predicate unique_seq(s: Seq<i8>) {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < i ==> s[i] != s[j]
}

struct UniqueBuilder {
    vec: Vec<i8>,
}

impl UniqueBuilder {
    predicate fn invariant(self) -> bool {
        unique_seq(self.vec@)
    }
    
    proof fn preserves_uniqueness(self, elem: i8) -> (unique_builder: Self)
        requires
            self.invariant(),
        ensures
            unique_builder.invariant(),
            if !contains(self.vec@, elem) {
                contains(unique_builder.vec@, elem)
            } else {
                unique_builder.vec@ =~= self.vec@
            }
    {
        if !contains(self.vec@, elem) {
            let mut new_vec = self.vec;
            new_vec.push(elem);
            proof {
                assert(new_vec@ =~= self.vec@.push(elem));
                assert forall|i: int, j: int| 0 <= i < new_vec@.len() && 0 <= j < i implies new_vec@[i] != new_vec@[j] by {
                    if i == new_vec@.len() - 1 {
                        assert(new_vec@[i] == elem);
                        assert forall|k: int| 0 <= k < self.vec@.len() implies self.vec@[k] != elem by {
                            assert(!contains(self.vec@, elem));
                        };
                    } else {
                        assert(self.invariant());
                    }
                };
            }
            UniqueBuilder { vec: new_vec }
        } else {
            self
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix predicate syntax by adding ! */
{
    let mut result = Vec::new();
    let mut builder = UniqueBuilder { vec: Vec::new() };
    
    let mut idx = 0;
    while idx < arr.len()
        invariant
            idx <= arr.len(),
            builder.invariant(),
            result@ =~= builder.vec@,
            forall|i: int| 0 <= i < arr@.len() ==> 
                contains(result@, arr@[i]) || 
                (idx <= i && !contains(result.subrange(0, idx as usize)@, arr@[i]))
        decreases arr.len() - idx
    {
        let elem = arr[idx];
        builder = builder.preserves_uniqueness(elem);
        
        if !contains(result@, elem) {
            let mut new_result = result;
            new_result.push(elem);
            result = new_result;
        }
        
        idx += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}