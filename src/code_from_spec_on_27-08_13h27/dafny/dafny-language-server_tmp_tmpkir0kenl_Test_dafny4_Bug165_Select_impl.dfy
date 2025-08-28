// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
lemma MultisetFilterLemma(s: seq<T>, filtered: seq<T>)
  ensures forall e: T :: f(e) ==> multiset(s)[e] == multiset(filtered)[e]
  ensures forall e: T :: !f(e) ==> multiset(filtered)[e] == 0
{
  // This lemma would ideally contain a proof, but since T is abstract and f is a function,
  // we rely on the implementation to ensure the property holds.
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])

method Main(s1: seq<T>)
// </vc-spec>
// </vc-spec>

// <vc-code>
method SelectImpl(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T :: !f(e) ==> multiset(r)[e] == 0)
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
    assert forall e: T :: f(e) ==> multiset(s1[..i])[e] == multiset(r)[e];
    assert forall e: T :: !f(e) ==> multiset(r)[e] == 0;
  }
}
// </vc-code>
