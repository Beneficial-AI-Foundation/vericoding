datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    result := [];
    return;
  }
  var res := [numbers[0]];
  var cur := numbers[0];
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j] >= numbers[j]
    invariant forall j :: 0 <= j + 1 < |res| ==> res[j] <= res[j + 1]
    invariant cur == res[i - 1]
  {
    var x := numbers[i];
    if x > cur {
      cur := x;
    }
    res := res + [cur];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

