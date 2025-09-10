use vstd::prelude::*;

verus! {

fn average(a: Vec<f32>, weights: Option<Vec<f32>>) -> (result: f32)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
        }
{
    assume(false);
    unreached();
}

}
fn main() {}