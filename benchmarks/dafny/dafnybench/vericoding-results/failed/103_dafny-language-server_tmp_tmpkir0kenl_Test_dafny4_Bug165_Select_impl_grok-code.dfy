// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])
{
  r := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall e: T :: f(e) ==> multiset(s1[..i])[e] == multiset(r)[e]
    invariant forall e: T :: !f(e) ==> multiset(r)[e] == 0
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])

method Main(s1: seq<T>)
// </vc-spec>
// <vc-code>
{
  var r: seq<T> := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall e: T :: f(e) ==> multiset(s1[..i])[e] == multiset(r)[e]
    invariant forall e: T :: !f(e) ==> multiset(r)[e] == 0
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

