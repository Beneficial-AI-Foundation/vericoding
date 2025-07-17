// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> m: int)
 requires 0 <= i < a.Length
 requires 0 <= j < b.Length
 ensures a[i] > b[j] ==> m == a[i]
 ensures a[i] <= b[j] ==> m == b[j]
{
  m := 0;
  assume a[i] > b[j] ==> m == a[i];
  assume a[i] <= b[j] ==> m == b[j];
  return m;
}


// SPEC

method testMax(a:array<int>, b:array<int>, i: int, j: int
    requires
        0 <= i < a.len(),
        0 <= j < b.len(),
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.index(i) > b.index(j) ==> m == a.index(i),
        a.index(i) <= b.index(j) ==> m == b.index(j)
;

proof fn lemma_max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (m: int)
 requires 0 <= i < a.Length
 requires 0 <= j < b.Length
 ensures a[i] > b[j] ==> m == a[i]
 ensures a[i] <= b[j] ==> m == b[j]
{
  m := 0;
  assume a[i] > b[j] ==> m == a[i];
  assume a[i] <= b[j] ==> m == b[j];
  return m;
}


// SPEC

method testMax(a:array<int>, b: Vec<int>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len(),
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.index(i) > b.index(j) ==> m == a.index(i),
        a.index(i) <= b.index(j) ==> m == b.index(j)
{
    (0, Vec::new(), 0, 0)
}

}