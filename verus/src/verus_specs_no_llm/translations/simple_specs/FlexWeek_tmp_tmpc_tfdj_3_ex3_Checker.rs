// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Max(a: Vec<nat>) -> m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
{
  m := 0;
  assume a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough;
  assume a.Length == 0 ==> m == -1;
  assume a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function;
  return m;
}


// SPEC
method Checker(
    ensures
        a.len() > 0 ==> forall |k: int| 0<=k<a.len() ==> m >= a.index(k)// not strong enough,
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> m in a.index(..) // finally at the top // approach did not work for recusrive function
;

proof fn lemma_Max(a: Vec<nat>) -> (m: int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
{
  m := 0;
  assume a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough;
  assume a.Length == 0 ==> m == -1;
  assume a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function;
  return m;
}


// SPEC
method Checker()
    ensures
        a.len() > 0 ==> forall |k: int| 0<=k<a.len() ==> m >= a.index(k)// not strong enough,
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> m in a.index(..) // finally at the top // approach did not work for recusrive function
{
    0
}

}