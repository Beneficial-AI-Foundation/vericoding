// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
function method multiset<T>(s: seq<T>): multiset<T>
{
  if s == [] then
    multiset{}
  else
    multiset{s[0]} + multiset(s[1..])
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
  var r_temp: seq<T> := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant (forall e: T  :: f(e) ==> multiset(s1[..i])[e] == multiset(r_temp)[e])
    invariant (forall e: T  :: (!f(e)) ==> multiset(r_temp)[e] == 0)
    invariant (forall e: T :: multiset(r_temp)[e] <= multiset(s1)[e]) // Added for better proof
  {
    if f(s1[i])
    {
      r_temp := r_temp + [s1[i]];
    }
    i := i + 1;
  }
  r := r_temp;
}
// </vc-code>

