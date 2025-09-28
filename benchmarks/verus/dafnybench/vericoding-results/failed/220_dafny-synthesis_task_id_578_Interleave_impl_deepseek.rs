use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn interleave_index_property(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>, i: int)
    requires
        0 <= i < s1.len(),
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures
        #[trigger] (3*i) < 3*s1.len(),
        #[trigger] (3*i + 1) < 3*s1.len(),
        #[trigger] (3*i + 2) < 3*s1.len(),
        (3*i) + 2 < 3*s1.len(),
{
    assert(3*i + 2 == 3*(i+1) - 1);
    assert(3*(i+1) - 1 <= 3*s1.len() - 1);
}

proof fn interleave_distinct_indices(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>)
    requires
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures
        forall|i: int, j: int| 
            0 <= i < s1.len() && 0 <= j < s1.len() && i != j ==>
            #[trigger] (3*i) != #[trigger] (3*j) && #[trigger] (3*i) != #[trigger] (3*j + 1) && #[trigger] (3*i) != #[trigger] (3*j + 2) &&
            #[trigger] (3*i + 1) != #[trigger] (3*j) && #[trigger] (3*i + 1) != #[trigger] (3*j + 1) && #[trigger] (3*i + 1) != #[trigger] (3*j + 2) &&
            #[trigger] (3*i + 2) != #[trigger] (3*j) && #[trigger] (3*i + 2) != #[trigger] (3*j + 1) && #[trigger] (3*i + 2) != #[trigger] (3*j + 2),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures 
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
// </vc-spec>
// <vc-code>
{
    let len: int = s1.len() as int;
    let mut result = Vec::<int>::new();
    let mut index: int = 0;
    
    while index < len
        invariant
            result@.len() == 3 * index,
            forall|i: int| 0 <= i < index ==> result@[3*i] == s1[i] && result@[3*i + 1] == s2[i] && result@[3*i + 2] == s3[i],
            index <= len,
            index >= 0,
    {
        result.push(s1[index as usize]);
        result.push(s2[index as usize]);
        result.push(s3[index as usize]);
        
        assert(result@.len() == 3 * (index + 1));
        
        proof {
            interleave_index_property(s1, s2, s3, index);
            
            assert forall|i: int| 0 <= i <= index implies result@[3*i] == s1[i] && result@[3*i + 1] == s2[i] && result@[3*i + 2] == s3[i] by {
                if i < index {
                    // Already established by invariant
                } else {
                    assert(i == index);
                    assert(result@[3*index] == s1[index]);
                    assert(result@[3*index + 1] == s2[index]);
                    assert(result@[3*index + 2] == s3[index]);
                }
            };
        }
        
        index = index + 1;
    }
    
    proof {
        interleave_distinct_indices(s1, s2, s3);
        assert(result@.len() == 3 * len);
    }
    
    seq![result] // Convert Vec to Seq using the seq! macro
}
// </vc-code>

fn main() {
}

}