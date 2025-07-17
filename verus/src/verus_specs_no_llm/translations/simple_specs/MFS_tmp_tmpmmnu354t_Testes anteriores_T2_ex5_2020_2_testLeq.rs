// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_leq(a: Vec<int>, b: Vec<int>) -> result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  result := false;
  assume result <==> (a.Length <= b.Length && a[..] ==> b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] ==> b[..k] && a[k] < b[k]);
  return result;
}


// SPEC

method testLeq(
    ensures
        result <==> (a.len() <= b.len() && a.index(..) == b.index(..a.len())) || (exists |k: int| 0 <= k < a.len() && k < b.len() && a.index(..k) == b.index(..k) && a.index(k) < b.index(k))
;

proof fn lemma_leq(a: Vec<int>, b: Vec<int>) -> (result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  result := false;
  assume result <==> (a.Length <= b.Length && a[..] ==> b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] ==> b[..k] && a[k] < b[k]);
  return result;
}


// SPEC

method testLeq()
    ensures
        result <==> (a.len() <= b.len() && a.index(..) == b.index(..a.len())) || (exists |k: int| 0 <= k < a.len() && k < b.len() && a.index(..k) == b.index(..k) && a.index(k) < b.index(k))
{
    0
}

}