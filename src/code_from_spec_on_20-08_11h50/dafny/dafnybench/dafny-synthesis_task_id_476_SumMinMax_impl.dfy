method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
// </vc-spec>
// <vc-code>
{
  var min := a[0];
  var max := a[0];
  var i := 1;
  
  MinBaseCase(a[..1]);
  MaxBaseCase(a[..1]);
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant min == Min(a[..i])
    invariant max == Max(a[..i])
  {
    if a[i] < min {
      min := a[i];
    }
    if a[i] > max {
      max := a[i];
    }
    
    MinInductive(a[..i+1], a[..i], Min(a[..i]), a[i]);
    MaxInductive(a[..i+1], a[..i], Max(a[..i]), a[i]);
    
    i := i + 1;
  }
  
  assert i == a.Length;
  assert a[..i] == a[..];
  
  sum := min + max;
}
// </vc-code>

// <vc-helpers>
lemma MinBaseCase(a: seq<int>)
    requires |a| == 1
    ensures Min(a) == a[0]
{
}

lemma MaxBaseCase(a: seq<int>)
    requires |a| == 1
    ensures Max(a) == a[0]
{
}

lemma MinInductive(full: seq<int>, prefix: seq<int>, minPrefix: int, newElem: int)
    requires |full| > 1
    requires |prefix| == |full| - 1
    requires full == prefix + [newElem]
    requires minPrefix == Min(prefix)
    ensures Min(full) == if newElem < minPrefix then newElem else minPrefix
{
    assert full[..|full|-1] == prefix;
    assert full[|full|-1] == newElem;
}

lemma MaxInductive(full: seq<int>, prefix: seq<int>, maxPrefix: int, newElem: int)
    requires |full| > 1
    requires |prefix| == |full| - 1
    requires full == prefix + [newElem]
    requires maxPrefix == Max(prefix)
    ensures Max(full) == if newElem > maxPrefix then newElem else maxPrefix
{
    assert full[..|full|-1] == prefix;
    assert full[|full|-1] == newElem;
}
// </vc-helpers>

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}