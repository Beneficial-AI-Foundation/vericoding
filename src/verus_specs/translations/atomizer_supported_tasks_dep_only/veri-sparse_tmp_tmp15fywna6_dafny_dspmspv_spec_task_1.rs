// ATOM 
pub fn sum(X_val: &[i32], X_crd: &[usize],
           v_val: &[i32], v_crd: &[usize], kX: usize, kV: usize, pX_end: usize, pV_end: usize) -> i32
    requires(
        X_val.len() == X_crd.len() &&
        pX_end <= X_crd.len() &&
        kX <= X_crd.len() &&
        v_val.len() == v_crd.len() &&
        pV_end <= v_crd.len() &&
        kV <= v_crd.len()
    )
{
}

// ATOM 
pub fn min(x: usize, y: usize) -> usize
{
}

// ATOM 
pub fn notin(y: usize, x: &[usize]) -> bool
{
}

// ATOM 
pub fn notin_seq(y: usize, x: &[usize]) -> bool
{
}

// ATOM 
pub fn index_seq(x: usize, y: &[usize]) -> usize
    ensures(|i: usize| 
        (i >= y.len() ==> notin_seq(x, y)) &&
        (i < y.len() ==> y[i as int] == x)
    )
{
}

// ATOM 
pub fn index(x: usize, y: &[usize]) -> usize
    ensures(|i: usize|
        (i >= y.len() ==> notin(x, y)) &&
        (i < y.len() ==> y[i as int] == x)
    )
{
}

// SPEC 
pub fn DSpMSpV(X_val: &[i32], X_crd: &[usize], X_pos: &[usize],
               X_crd1: &[usize], X_len: usize,
               v_val: &[i32], v_crd: &[usize]) -> Vec<i32>
    requires(
        X_pos.len() >= 1 &&
        X_val.len() == X_crd.len() &&
        (forall|i: usize, j: usize| 0 <= i && i < j && j < X_pos.len() ==> X_pos[i as int] <= X_pos[j as int]) &&
        (forall|i: usize| 0 <= i && i < X_pos.len() ==> X_pos[i as int] <= X_val.len()) &&
        X_len >= X_crd1.len() &&
        (forall|i: usize| 0 <= i && i < X_crd1.len() ==> X_crd1[i as int] < X_len) &&
        X_crd1.len() < X_pos.len() &&
        (forall|i: usize, j: usize| 0 <= i && i < j && j < X_crd1.len() ==> X_crd1[i as int] < X_crd1[j as int]) &&
        v_val.len() == v_crd.len()
    )
    ensures(|y: Vec<i32>|
        y.len() == X_len &&
        (forall|i: usize| 0 <= i && i < y.len() ==>
            y[i as int] == 
                if index(i, X_crd1) < X_crd1.len() {
                    sum(X_val, X_crd, v_val, v_crd, X_pos[index(i, X_crd1) as int], 0, X_pos[(index(i, X_crd1)+1) as int], v_val.len())
                } else {
                    0
                }
        )
    )
{
}