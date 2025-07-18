use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Find maximum value in a non-empty vector
fn Max(a: Vec<nat>) -> (m: nat)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= m
    ensures exists|i: int| 0 <= i < a.len() && m == a[i]
{
    let mut m = a[0];
    let mut index = 1;
    
    while index < a.len()
        invariant 
            1 <= index <= a.len(),
            forall|i: int| 0 <= i < index ==> a[i] <= m,
            exists|i: int| 0 <= i < index && m == a[i],
    {
        if a[index as int] > m {
            m = a[index as int];
        }
        index = index + 1;
    }
    m
}

// Compute cube of a natural number
fn Cube(n: nat) -> (c: nat) 
    ensures c == n * n * n
{
    n * n * n
}

// Recursive power function (2^n)
spec fn Power(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

// Compute 2^N iteratively
fn ComputePower(N: nat) -> (y: nat)
    ensures y == Power(N)
{
    let mut result = 1;
    let mut i = 0;
    
    while i < N
        invariant 
            0 <= i <= N,
            result == Power(i),
    {
        result = result * 2;
        i = i + 1;
        assert(i > 0);
        assert(Power(i) == 2 * Power((i - 1) as nat));
    }
    result
}

// Find maximum in array, return 0 if empty
fn MaxArray(a: Vec<nat>) -> (m: nat)
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= m
    ensures (m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a[i]
{
    if a.len() == 0 {
        0
    } else {
        let mut m = a[0];
        let mut index = 1;
        
        while index < a.len()
            invariant 
                1 <= index <= a.len(),
                forall|i: int| 0 <= i < index ==> a[i] <= m,
                exists|i: int| 0 <= i < index && m == a[i],
        {
            if a[index as int] > m {
                m = a[index as int];
            }
            index = index + 1;
        }
        m
    }
}

// Increment all elements in a 2D array
fn IncrementMatrix(a: &mut Vec<Vec<int>>)
    requires 
        old(a).len() > 0,
        forall|i: int| 0 <= i < old(a).len() ==> old(a)[i].len() == old(a)[0].len(),
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == old(a)[i].len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> 
            a[i][j] == old(a)[i][j] + 1,
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old(a).len(),
            forall|k: int| 0 <= k < a.len() ==> a[k].len() == old(a)[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < a[k].len() ==> 
                a[k][j] == old(a)[k][j] + 1,
            forall|k: int, j: int| i <= k < a.len() && 0 <= j < a[k].len() ==> 
                a[k][j] == old(a)[k][j],
    {
        let mut j = 0;
        while j < a[i as int].len()
            invariant
                0 <= i < a.len(),
                0 <= j <= a[i as int].len(),
                a.len() == old(a).len(),
                forall|k: int| 0 <= k < a.len() ==> a[k].len() == old(a)[k].len(),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < a[k].len() ==> 
                    a[k][l] == old(a)[k][l] + 1,
                forall|l: int| 0 <= l < j ==> a[i as int][l] == old(a)[i as int][l] + 1,
                forall|l: int| j <= l < a[i as int].len() ==> a[i as int][l] == old(a)[i as int][l],
                forall|k: int, l: int| i < k < a.len() && 0 <= l < a[k].len() ==> 
                    a[k][l] == old(a)[k][l],
        {
            let old_val = a[i as int][j as int];
            a.index_mut(i as usize).set(j as usize, old_val + 1);
            j = j + 1;
        }
        i = i + 1;
    }
}

// Copy one 2D array to another
fn CopyMatrix(src: &Vec<Vec<int>>, dst: &mut Vec<Vec<int>>)
    requires 
        src.len() > 0,
        old(dst).len() == src.len(),
        forall|i: int| 0 <= i < src.len() ==> src[i].len() == src[0].len(),
        forall|i: int| 0 <= i < old(dst).len() ==> old(dst)[i].len() == src[0].len(),
    ensures 
        dst.len() == src.len(),
        forall|i: int| 0 <= i < dst.len() ==> dst[i].len() == src[i].len(),
        forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src[i].len() ==> 
            dst[i][j] == src[i][j],
{
    let mut i = 0;
    while i < src.len()
        invariant
            0 <= i <= src.len(),
            dst.len() == src.len(),
            forall|k: int| 0 <= k < dst.len() ==> dst[k].len() == src[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < src[k].len() ==> 
                dst[k][j] == src[k][j],
    {
        let mut j = 0;
        while j < src[i as int].len()
            invariant
                0 <= i < src.len(),
                0 <= j <= src[i as int].len(),
                dst.len() == src.len(),
                forall|k: int| 0 <= k < dst.len() ==> dst[k].len() == src[k].len(),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < src[k].len() ==> 
                    dst[k][l] == src[k][l],
                forall|l: int| 0 <= l < j ==> dst[i as int][l] == src[i as int][l],
        {
            let val = src[i as int][j as int];
            dst.index_mut(i as usize).set(j as usize, val);
            j = j + 1;
        }
        i = i + 1;
    }
}

}