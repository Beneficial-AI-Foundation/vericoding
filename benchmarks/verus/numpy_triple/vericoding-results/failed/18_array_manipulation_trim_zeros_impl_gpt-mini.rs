// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents the trim mode for trim_zeros function */
#[derive(Eq, PartialEq)]
pub enum TrimMode {
    /* Trim zeros from the front of the array only (corresponds to 'f') */
    Front,
    /* Trim zeros from the back of the array only (corresponds to 'b') */
    Back,
    /* Trim zeros from both front and back of the array (corresponds to 'fb', default) */
    Both,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): find_first_nonzero finds index of first non-zero element or None */
pub fn find_first_nonzero(arr: &Vec<f32>) -> Option<int>
    ensures
        match result {
            None => forall|i: int| 0 <= i < arr@.len() ==> arr@[i] == 0.0f32,
            Some(k) => 0 <= k < arr@.len() && arr@[k] != 0.0f32 && forall|i: int| 0 <= i < k ==> arr@[i] == 0.0f32,
        }
{
    let n_usize = arr.len();
    let n_int: int = arr@.len();
    let mut i_usize: usize = 0usize;
    let mut i_int: int = 0;
    while i_int < n_int
        invariant
            i_int >= 0,
            i_int <= n_int,
            i_usize == i_int as usize,
        decreases n_int - i_int
    {
        let v = arr[i_usize];
        if v != 0.0f32 {
            return Some(i_int);
        }
        i_usize += 1;
        i_int += 1;
    }
    None
}

/* helper modified by LLM (iteration 2): find_last_nonzero finds index of last non-zero element or None */
pub fn find_last_nonzero(arr: &Vec<f32>) -> Option<int>
    ensures
        match result {
            None => forall|i: int| 0 <= i < arr@.len() ==> arr@[i] == 0.0f32,
            Some(k) => 0 <= k < arr@.len() && arr@[k] != 0.0f32 && forall|i: int| k < i && i < arr@.len() ==> arr@[i] == 0.0f32,
        }
{
    let n_usize = arr.len();
    let n_int: int = arr@.len();
    let mut i_usize: usize = n_usize;
    let mut i_int: int = n_int;
    while i_int > 0
        invariant
            i_int >= 0,
            i_int <= n_int,
            i_usize == i_int as usize,
        decreases i_int
    {
        i_usize -= 1;
        i_int -= 1;
        let v = arr[i_usize];
        if v != 0.0f32 {
            return Some(i_int);
        }
    }
    None
}

// </vc-helpers>

// <vc-spec>
fn trim_zeros(arr: Vec<f32>, mode: TrimMode) -> (result: Vec<f32>)
    ensures
        result@.len() <= arr@.len(),
        /* Result contains only elements from the original array */
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == arr@[j],
        /* Basic trimming properties based on mode */
        (mode == TrimMode::Front ==> 
            (result@.len() == 0 || result@[0] != 0.0f32)),
        (mode == TrimMode::Back ==> 
            (result@.len() == 0 || result@[result@.len() - 1] != 0.0f32)),
        (mode == TrimMode::Both ==> 
            (result@.len() == 0 || (result@[0] != 0.0f32 && result@[result@.len() - 1] != 0.0f32)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement trim_zeros using helper functions */
    match mode {
        TrimMode::Front => {
            let opt = find_first_nonzero(&arr);
            match opt {
                None => Vec::new(),
                Some(k) => {
                    let n_int: int = arr@.len();
                    let mut res: Vec<f32> = Vec::new();
                    let mut i_int: int = k;
                    let mut i_usize: usize = k as usize;
                    while i_int < n_int
                        invariant
                            0 <= i_int,
                            i_int <= n_int,
                            i_usize == i_int as usize,
                        decreases n_int - i_int
                    {
                        res.push(arr[i_usize]);
                        i_usize += 1;
                        i_int += 1;
                    }
                    res
                }
            }
        }
        TrimMode::Back => {
            let opt = find_last_nonzero(&arr);
            match opt {
                None => Vec::new(),
                Some(k) => {
                    let mut res: Vec<f32> = Vec::new();
                    let mut i_int: int = 0;
                    let n_int: int = arr@.len();
                    let mut i_usize: usize = 0usize;
                    while i_int <= k
                        invariant
                            0 <= i_int,
                            i_int <= n_int,
                            i_usize == i_int as usize,
                        decreases k - i_int
                    {
                        res.push(arr[i_usize]);
                        i_usize += 1;
                        i_int += 1;
                    }
                    res
                }
            }
        }
        TrimMode::Both => {
            let opt_f = find_first_nonzero(&arr);
            match opt_f {
                None => Vec::new(),
                Some(f) => {
                    let opt_l = find_last_nonzero(&arr);
                    match opt_l {
                        Some(l) => {
                            let mut res: Vec<f32> = Vec::new();
                            let mut i_int: int = f;
                            let n_int: int = arr@.len();
                            let mut i_usize: usize = f as usize;
                            while i_int <= l
                                invariant
                                    0 <= i_int,
                                    i_int <= n_int,
                                    i_usize == i_int as usize,
                                decreases l - i_int
                            {
                                res.push(arr[i_usize]);
                                i_usize += 1;
                                i_int += 1;
                            }
                            res
                        }
                        None => Vec::new(),
                    }
                }
            }
        }
    }
}

// </vc-code>


}
fn main() {}