class List<T(0)> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>

  var a: array<T>
  var n: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    a in Repr &&
    n <= a.Length &&
    Contents == a[..n]
  }

// <vc-spec>
  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {
    Contents, n := [], 0;
    a := new T[0];
    Repr := {this, a};
  }

// <vc-helpers>
// </vc-helpers>

method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
// </vc-spec>
// <vc-code>
{
  if n == a.Length {
    // Need to resize the array
    var newSize := if a.Length == 0 then 1 else 2 * a.Length;
    var newArray := new T[newSize];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant i <= a.Length
      invariant i <= newArray.Length
      invariant forall j :: 0 <= j < i ==> newArray[j] == a[j]
    {
      newArray[i] := a[i];
      i := i + 1;
    }
    a := newArray;
    Repr := {this, a};
  }
  
  a[n] := t;
  Contents := Contents + [t];
  n := n + 1;
}
// </vc-code>

}

class Cell { var data: int }

iterator M<T(0)>(l: List<T>, c: Cell) yields (x: T)
  requires l.Valid()
  reads l.Repr
  modifies c
  yield requires true
  yield ensures xs <= l.Contents  // this is needed in order for the next line to be well-formed
  yield ensures x == l.Contents[|xs|-1]
  ensures xs == l.Contents
{
  var i := 0;
  while i < l.n
    invariant i <= l.n && i == |xs| && xs <= l.Contents
  {
    if (*) { assert l.Valid(); }  // this property is maintained, due to the reads clause
    if (*) {
      x := l.a[i]; yield;  // or, equivalently, 'yield l.a[i]'
      i := i + 1;
    } else {
      x, i := l.a[i], i + 1;
      yield;
    }
  }
}

method Client<T(==,0)>(l: List, stop: T) returns (s: seq<T>)
  requires l.Valid()
{
  var c := new Cell;
  var iter := new M(l, c);
  s := [];
  while true
    invariant iter.Valid() && fresh(iter._new)
    invariant iter.xs <= l.Contents
    decreases |l.Contents| - |iter.xs|
  {
    var more := iter.MoveNext();
    if (!more) { break; }
    s := s + [iter.x];
    if (iter.x == stop) { return; }  // if we ever see 'stop', then just end
  }
}

method PrintSequence<T>(s: seq<T>)
{
  var i := 0;
  while i < |s|
  {
    print s[i], " ";
    i := i + 1;
  }
  print "\n";
}