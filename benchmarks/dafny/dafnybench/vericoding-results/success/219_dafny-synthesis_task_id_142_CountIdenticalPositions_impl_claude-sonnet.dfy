

// <vc-helpers>
lemma SetSizeIncrement(a: seq<int>, b: seq<int>, c: seq<int>, i: int)
    requires 0 <= i < |a| && |a| == |b| && |b| == |c|
    requires a[i] == b[i] && b[i] == c[i]
    ensures | set j: int | 0 <= j < i+1 && a[j] == b[j] && b[j] == c[j]| == 
            | set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]| + 1
{
    var S1 := set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j];
    var S2 := set j: int | 0 <= j < i+1 && a[j] == b[j] && b[j] == c[j];
    
    assert S2 == S1 + {i};
    assert i !in S1;
}

lemma SetSizeNoChange(a: seq<int>, b: seq<int>, c: seq<int>, i: int)
    requires 0 <= i < |a| && |a| == |b| && |b| == |c|
    requires !(a[i] == b[i] && b[i] == c[i])
    ensures | set j: int | 0 <= j < i+1 && a[j] == b[j] && b[j] == c[j]| == 
            | set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]|
{
    var S1 := set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j];
    var S2 := set j: int | 0 <= j < i+1 && a[j] == b[j] && b[j] == c[j];
    
    assert S2 == S1;
}
// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]|
  {
    if a[i] == b[i] && b[i] == c[i] {
      SetSizeIncrement(a, b, c, i);
      count := count + 1;
    } else {
      SetSizeNoChange(a, b, c, i);
    }
    i := i + 1;
  }
}
// </vc-code>

