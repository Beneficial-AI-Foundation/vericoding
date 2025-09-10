use vstd::prelude::*;

verus! {

#[derive(PartialEq)]
pub struct Complex {
    pub real: f32,
    pub imag: f32,
}

fn hfft(a: Vec<Complex>, m: usize) -> (result: Vec<f32>)
    requires 
        m > 0,
        a.len() == m + 1,
    ensures
        result.len() == 2 * m,
{
    assume(false);
    unreached();
}

}
fn main() {}