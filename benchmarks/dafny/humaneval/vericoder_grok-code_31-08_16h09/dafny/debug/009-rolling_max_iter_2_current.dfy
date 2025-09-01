datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>

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
  } else {
    var current_max := numbers[0];
    result := [current_max];
    var i := 1;
    while i < |numbers|
      invariant |result| == i
      invariant 0 <= i <= |numbers|
      invariant forall j :: 0 <= j + 1 < i ==> result[j] <= result[j + 1]
      invariant forall k :: 0 <= k < i ==> numbers[k] <= result[k]
    {
      current_max := if current_max < numbers[i] then numbers[i] else current_max;
      result := result + [current_max];
      i := i + 1;
    }
  }
}
// </vc-code>

