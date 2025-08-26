method Select<T>(s1: seq<T>, f: T -> bool) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])
{
  r := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant (forall e: T :: f(e) ==> multiset(r)[e] <= multiset(s1[..i])[e])
    invariant (forall e: T :: !f(e) ==> multiset(r)[e] == 0)
    invariant (forall e: T :: f(e) ==> multiset(r)[e] == multiset(s1[..i])[e] - multiset(s1[i..])[e])
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
}

method Main<T>(s1: seq<T>)
// </vc-spec>