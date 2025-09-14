// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
lemma FilterSequenceLemma(s: seq<T>, e: T)
  ensures f(e) ==> multiset(s)[e] == multiset([s[i] | i := 0 to |s| where f(s[i])])[e]
  ensures !f(e) ==> multiset([s[i] | i := 0 to |s| where f(s[i])])[e] == 0
{
  if f(e) {
    assert forall i | 0 <= i < |s| && f(s[i]) :: s[i] in multiset(s);
    assert forall i | 0 <= i < |s| && !f(s[i]) :: s[i] !in multiset([s[i] | i := 0 to |s| where f(s[i])]);
  } else {
    assert forall i | 0 <= i < |s| :: f(s[i]) ==> s[i] != e;
  }
}

ghost predicate ValidSequence(s: seq<T>, i: int, r: seq<T>)
  requires 0 <= i <= |s|
{
  multiset(r) == multiset([s[j] | j := 0 to i where f(s[j])]) &&
  (forall e: T :: f(e) ==> multiset(s[0..i])[e] == multiset(r)[e]) &&
  (forall e: T :: !f(e) ==> 0 == multiset(r)[e])
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
  r := [];
  var i := 0;
  
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant multiset(r) == multiset([s1[j] | j := 0 to i where f(s1[j])])
    invariant (forall e: T :: f(e) ==> multiset(s1[0..i])[e] == multiset(r)[e])
    invariant (forall e: T :: !f(e) ==> 0 == multiset(r)[e])
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

