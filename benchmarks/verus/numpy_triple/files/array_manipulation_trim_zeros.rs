use vstd::prelude::*;

verus! {

pub enum TrimMode {

    Front,

    Back,

    Both,
}

fn trim_zeros(arr: Vec<f64>, mode: TrimMode) -> (result: Vec<f64>)
    ensures
        exists|start: int, finish: int|
            0 <= start <= arr.len() &&
            0 <= finish <= arr.len() &&
            start <= finish &&
            result.len() == (finish - start) &&

            (matches!(mode, TrimMode::Front | TrimMode::Both) ==> 
                forall|i: int| 0 <= i < start ==> arr[i] == 0.0) &&

            (matches!(mode, TrimMode::Back | TrimMode::Both) ==> 
                forall|i: int| finish <= i < arr.len() ==> arr[i] == 0.0) &&

            (forall|i: int| 0 <= i < result.len() ==> result[i] == arr[start + i]) &&

            (matches!(mode, TrimMode::Front | TrimMode::Both) ==> 
                (start == arr.len() || arr[start] != 0.0)) &&

            (matches!(mode, TrimMode::Back | TrimMode::Both) ==> 
                (finish == 0 || (finish > 0 && arr[finish - 1] != 0.0)))
{
    assume(false);
    unreached();
}

}
fn main() {}