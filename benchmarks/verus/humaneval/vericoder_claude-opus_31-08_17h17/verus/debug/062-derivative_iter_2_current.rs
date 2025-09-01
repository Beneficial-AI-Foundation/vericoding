use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    if xs.len() == 0 {
        return None;
    }
    
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 1;
    
    while i < xs.len()
        invariant
            1 <= i <= xs.len(),
            result@.len() == i - 1,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] result@[j] as int == j + 1 < xs@.len() && (j + 1) * xs@[j + 1] as int == result@[j] as int,
        decreases xs.len() - i,
    {
        let val = i * xs[i];
        result.push(val);
        i = i + 1;
    }
    
    assert(result@.len() == xs@.len() - 1);
    assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j] as int == (j + 1) * xs@[j + 1] as int by {
        assert(0 <= j < xs@.len() - 1);
    }
    
    assert(xs@.map(|i: int, x| i * x).skip(1) =~= result@.map_values(|x| x as int)) by {
        assert(xs@.map(|i: int, x| i * x).skip(1).len() == result@.len());
        assert forall|k: int| 0 <= k < result@.len() implies 
            #[trigger] xs@.map(|i: int, x| i * x).skip(1)[k] == result@.map_values(|x| x as int)[k] by {
            assert(xs@.map(|i: int, x| i * x).skip(1)[k] == xs@.map(|i: int, x| i * x)[k + 1]);
            assert(xs@.map(|i: int, x| i * x)[k + 1] == (k + 1) * xs@[k + 1]);
            assert(result@[k] as int == (k + 1) * xs@[k + 1] as int);
            assert(result@.map_values(|x| x as int)[k] == result@[k] as int);
        }
    }
    
    Some(result)
}
// </vc-code>

fn main() {}
}