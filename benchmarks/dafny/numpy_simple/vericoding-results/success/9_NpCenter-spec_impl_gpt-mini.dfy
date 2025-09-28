// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function StartPos(width: int, len: int): int {
  (width - len + 1) / 2
}

/* helper modified by LLM (iteration 2): Spaces with length property */
function Spaces(n: int): string
  requires n >= 0
  decreases n
  ensures |Spaces(n)| == n
{
  if n == 0 then "" else " " + Spaces(n - 1)
}

/* helper modified by LLM (iteration 2): StartPosNonneg lemma ensures start >= 0 and start+len <= width */
lemma StartPosNonneg(width: int, len: int)
  requires width > len
  requires len >= 0
  ensures StartPos(width,len) >= 0
  ensures StartPos(width,len) + len <= width
{
  var s := StartPos(width, len);
  var t := width - len;
  assert t >= 1;
  // From s = (t + 1) / 2 we have 2*s <= t + 1
  assert 2 * s <= t + 1;
  // Since t >= 1 we have t + 1 <= 2*t
  assert t + 1 <= 2 * t;
  // Combine to get 2*s <= 2*t, hence s <= t
  assert 2 * s <= 2 * t;
  assert s <= t;
  assert s >= 0;
  assert s + len <= width;
}

// </vc-helpers>

// <vc-spec>
method Center(input: array<string>, width: int) returns (result: array<string>)
    requires 
        input.Length > 0
    requires
        forall i :: 0 <= i < input.Length ==> |input[i]| >= 1
    ensures
        result.Length == input.Length
    ensures
        forall i :: 0 <= i < input.Length ==> 
            if |input[i]| > width then
                |result[i]| == |input[i]|
            else
                |result[i]| == width
    ensures
        forall i :: 0 <= i < input.Length ==> 
            if |input[i]| < width then
                var start_pos := (width - |input[i]| + 1) / 2;
                result[i][start_pos..start_pos + |input[i]|] == input[i]
            else
                true
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement centering using helpers and assert lengths */
  result := new string[input.Length];
  var i := 0;
  while i < input.Length
    invariant 0 <= i <= input.Length
    invariant result.Length == input.Length
    invariant forall k :: 0 <= k < i ==> (if |input[k]| > width then |result[k]| == |input[k]| else |result[k]| == width)
    invariant forall k :: 0 <= k < i ==> (if |input[k]| < width then var start_pos := (width - |input[k]| + 1) / 2; result[k][start_pos..start_pos + |input[k]|] == input[k] else true)
  {
    var s := |input[i]|;
    if s < width {
      var start := StartPos(width, s);
      StartPosNonneg(width, s);
      var left := Spaces(start);
      var right := Spaces(width - start - s);
      assert |left| == start;
      assert |right| == width - start - s;
      result[i] := left + input[i] + right;
      assert |result[i]| == |left| + s + |right|;
      assert |result[i]| == start + s + (width - start - s);
      assert |result[i]| == width;
      assert result[i][start..start + s] == input[i];
    } else {
      result[i] := input[i];
    }
    i := i + 1;
  }
  return result;
}

// </vc-code>
