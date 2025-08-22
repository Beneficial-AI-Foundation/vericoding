//ATOM
method Max(a:array<nat>)returns(m:int)
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
{
}
