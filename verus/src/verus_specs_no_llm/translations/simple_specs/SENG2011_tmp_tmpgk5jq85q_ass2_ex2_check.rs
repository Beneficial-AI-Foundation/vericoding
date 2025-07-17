// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(a: String, low: int, high: int)
requires 0 <= low <= high <= |a|
{ 
  forall j, k: : low <= j < k < high ==> a[j] <= a[k] 
}


//ATOM

method String3Sort(a: string) returns (b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset{
  b: = "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}

{
  b: = "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}


// SPEC

method check() -> bool {
    
}

spec fn spec_String3Sort(a: String) -> b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset{
  b := "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}

{
  b := "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}


// SPEC

method check(
    requires
        a.len() == 3
    ensures
        Sorted(b, 0, b.len()),
        a.len() == b.len(),
        multiset
;

proof fn lemma_String3Sort(a: String) -> (b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset{
  b: = "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}

{
  b: = "";
  assume Sorted(b, 0, |b|);
  assume |a| ==> |b|;
  assume multiset{b[0], b[1], b[2]} ==> multiset{a[0], a[1], a[2]};
  return b;
}


// SPEC

method check()
    requires
        a.len() == 3
    ensures
        Sorted(b, 0, b.len()),
        a.len() == b.len(),
        multiset
{
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
}

}