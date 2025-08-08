use vstd::prelude::*;

verus! {

fn center(input: Vec<String>, width: usize) -> (res: Vec<String>)
    requires 
        forall|i: int| 0 <= i < input.len() ==> input[i]@.len() >= 1,
        width > 0,
    ensures 
        res.len() == input.len()
{
    let mut res: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < input.len()
        invariant 
            res.len() == i,
            i <= input.len()
        decreases input.len() - i
    {
        res.push(input[i].clone());
        i += 1;
    }
    
    res
}

}

fn main() {}