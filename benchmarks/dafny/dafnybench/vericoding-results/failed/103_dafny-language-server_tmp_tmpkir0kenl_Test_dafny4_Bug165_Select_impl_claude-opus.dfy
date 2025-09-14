// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
lemma SelectPreservesMultiset(s: seq<T>, r: seq<T>, i: nat)
  requires i <= |s|
  requires r == SelectHelper(s, i)
  ensures forall e: T :: f(e) ==> multiset(s[i..])[e] == multiset(r)[e]
  ensures forall e: T :: !f(e) ==> multiset(r)[e] == 0
{
  if i == |s| {
    assert s[i..] == [];
    assert r == [];
  } else {
    var rest := SelectHelper(s, i + 1);
    SelectPreservesMultiset(s, rest, i + 1);
    
    if f(s[i]) {
      assert r == [s[i]] + rest;
      assert s[i..] == [s[i]] + s[i+1..];
      
      forall e: T
      ensures f(e) ==> multiset(s[i..])[e] == multiset(r)[e]
      ensures !f(e) ==> multiset(r)[e] == 0
      {
        if f(e) {
          if e == s[i] {
            calc {
              multiset(r)[e];
              == multiset([s[i]] + rest)[e];
              == multiset([s[i]])[e] + multiset(rest)[e];
              == 1 + multiset(rest)[e];
              == 1 + multiset(s[i+1..])[e];
              == multiset([s[i]])[e] + multiset(s[i+1..])[e];
              == multiset([s[i]] + s[i+1..])[e];
              == multiset(s[i..])[e];
            }
          } else {
            calc {
              multiset(r)[e];
              == multiset([s[i]] + rest)[e];
              == multiset([s[i]])[e] + multiset(rest)[e];
              == 0 + multiset(rest)[e];
              == multiset(s[i+1..])[e];
              == multiset(s[i..])[e];
            }
          }
        } else {
          assert multiset(rest)[e] == 0;
          assert e != s[i];
          assert multiset([s[i]])[e] == 0;
        }
      }
    } else {
      assert r == rest;
      assert s[i..] == [s[i]] + s[i+1..];
      
      forall e: T
      ensures f(e) ==> multiset(s[i..])[e] == multiset(r)[e]
      ensures !f(e) ==> multiset(r)[e] == 0
      {
        if f(e) {
          assert e != s[i];
          calc {
            multiset(r)[e];
            == multiset(rest)[e];
            == multiset(s[i+1..])[e];
            == multiset(s[i..])[e];
          }
        } else {
          assert multiset(r)[e] == multiset(rest)[e] == 0;
        }
      }
    }
  }
}

function SelectHelper(s: seq<T>, i: nat): seq<T>
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then []
  else if f(s[i]) then [s[i]] + SelectHelper(s, i + 1)
  else SelectHelper(s, i + 1)
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
  var result := SelectHelper(s1, 0);
  assert s1[0..] == s1;
  SelectPreservesMultiset(s1, result, 0);
  return result;
}
// </vc-code>

