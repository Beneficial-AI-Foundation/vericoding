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
// </vc-helpers>

// <vc-spec>
method solve(input: seq<int>) returns (result: seq<int>)
    requires |input| >= 2
    ensures |result| == |input|
    ensures forall i :: 0 <= i < |input| ==> result[i] == max_excluding(input, i)
// </vc-spec>
// <vc-code>
var left_max := [input[0]];
  for i := 1 to |input|-1
    {
      var temp := if left_max[i-1] > input[i] then left_max[i-1] else input[i];
      left_max := left_max + [temp];
    }

  var right_max := [];
  for i := |input|-1 downto 0
    {
      if right_max == [] 
      {
        right_max := [input[i]];
      }
      else 
      {
        var curr := if right_max[0] > input[i] then right_max[0] else input[i];
        right_max := [curr] + right_max;
      }
    }

  result := [];
  for i := 0 to |input|-1
    {
      var excl_max: int;
      if i == 0 
      {
        excl_max := right_max[1];
      }
      else if i == |input|-1 
      {
        excl_max := left_max[i-1];
      }
      else 
      {
        excl_max := if left_max[i-1] > right_max[i+1] then left_max[i-1] else right_max[i+1];
      }
      result := result + [excl_max];
    }
// </vc-code>

