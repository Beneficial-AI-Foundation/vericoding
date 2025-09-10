function max_of_seq(s: seq<int>): int
    requires |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_of_seq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max_of_seq(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= max_of_seq(s[1..]) then s[0]
    else max_of_seq(s[1..])
}

function max_excluding(s: seq<int>, exclude_idx: int): int
    requires 0 <= exclude_idx < |s|
    requires |s| >= 2
{
    var others := s[..exclude_idx] + s[exclude_idx+1..];
    max_of_seq(others)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: seq<int>) returns (result: seq<int>)
    requires |input| >= 2
    ensures |result| == |input|
    ensures forall i :: 0 <= i < |input| ==> result[i] == max_excluding(input, i)
// </vc-spec>
// <vc-code>
{
  var n := |input|;
  var resArr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> resArr[k] == max_excluding(input, k)
    decreases n - i
  {
    resArr[i] := max_excluding(input, i);
    i := i + 1;
  }
  result := resArr[..];
}
// </vc-code>

