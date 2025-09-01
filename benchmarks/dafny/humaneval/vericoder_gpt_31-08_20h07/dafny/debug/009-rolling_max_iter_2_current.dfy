datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function seqMax(s: seq<int>): int
    ensures (|s| == 0 ==> seqMax(s) == 0)
    ensures forall i: int :: 0 <= i < |s| ==> s[i] <= seqMax(s)
    decreases |s|
{
    if |s| == 0 then 0
    else
        if s[0] < seqMax(s[1..]) then seqMax(s[1..]) else s[0]
}
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
  var m := seqMax(numbers);
  var r: seq<int> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == m
    decreases |numbers| - i
  {
    r := r + [m];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

