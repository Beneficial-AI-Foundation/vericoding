// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type T
function f(a: T) : bool

// <vc-helpers>
lemma FilterPreservesMultiset(s: seq<T>, r: seq<T>)
  requires r == FilterSeq(s)
  ensures forall e: T :: f(e) ==> multiset(s)[e] == multiset(r)[e]
  ensures forall e: T :: !f(e) ==> multiset(r)[e] == 0
{
  if |s| == 0 {
    assert r == [];
  } else {
    var head := s[0];
    var tail := s[1..];
    var filteredTail := FilterSeq(tail);
    
    if f(head) {
      assert r == [head] + filteredTail;
      FilterPreservesMultiset(tail, filteredTail);
    } else {
      assert r == filteredTail;
      FilterPreservesMultiset(tail, filteredTail);
    }
  }
}

function FilterSeq(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else if f(s[0]) then [s[0]] + FilterSeq(s[1..])
  else FilterSeq(s[1..])
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
  var result := FilterSeq(s1);
  FilterPreservesMultiset(s1, result);
  return result;
}
// </vc-code>

