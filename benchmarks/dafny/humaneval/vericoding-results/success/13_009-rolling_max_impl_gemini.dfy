// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)

    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
// </vc-spec>
// <vc-code>
{
  result := [];
  if |numbers| > 0 {
    var running_max := numbers[0];
    result := [running_max];
    var i := 1;
    while i < |numbers|
      invariant 1 <= i <= |numbers|
      invariant |result| == i
      invariant result[i-1] == running_max
      invariant forall j :: 0 <= j < i ==> numbers[j] <= result[j]
      invariant forall j :: 0 <= j < i-1 ==> result[j] <= result[j+1]
      invariant forall j :: 0 <= j < i ==> running_max >= numbers[j]
    {
      running_max := max(running_max, numbers[i]);
      result := result + [running_max];
      i := i + 1;
    }
  }
}
// </vc-code>
