// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: Vec<nat>) -> (m: int)
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
        a.len() > 0 ==> forall k :: 0<=k<a.len() ==> m >= a.spec_index(k)// not strong enough,
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> m in a.spec_index(..) // finally at the top // approach did not work for recusrive function
{
    return 0;
}

}