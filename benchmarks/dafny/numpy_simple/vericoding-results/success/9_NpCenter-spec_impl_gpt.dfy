// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed to 'function' (not 'function method'); builds a string of n spaces */
function Spaces(n: nat): string
  ensures |Spaces(n)| == n
  ensures forall k: int :: 0 <= k < |Spaces(n)| ==> Spaces(n)[k] == ' '
  decreases n
{
  if n == 0 then "" else " " + Spaces(n - 1)
}

/* helper modified by LLM (iteration 2): Lemma to extract middle substring from a triple concatenation */
lemma MiddleSlice(a: string, b: string, c: string)
  ensures (a + b + c)[|a| .. |a| + |b|] == b
{
  assert a + b + c == a + (b + c);
  assert (a + b + c)[|a| .. |a| + |b|] == (a + (b + c))[|a| .. |a| + |b|];
  assert (a + (b + c))[|a| .. |a| + |b|] == (b + c)[0 .. |b|];
  assert (b + c)[0 .. |b|] == b;
  assert (a + b + c)[|a| .. |a| + |b|] == b;
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
  /* code modified by LLM (iteration 2): Implement centering using Spaces and prove substring placement */
  result := new string[input.Length];
  var i := 0;
  while i < input.Length
    invariant 0 <= i <= input.Length
    invariant result.Length == input.Length
    invariant forall j :: 0 <= j < i ==>
      if |input[j]| > width then |result[j]| == |input[j]| else |result[j]| == width
    invariant forall j :: 0 <= j < i ==>
      if |input[j]| < width then
        var start_pos := (width - |input[j]| + 1) / 2;
        result[j][start_pos..start_pos + |input[j]|] == input[j]
      else
        true
  {
    var s := input[i];
    var len := |s|;
    if width < 0 || len > width {
      result[i] := s;
    } else {
      var d := width - len;
      assert d >= 0;
      var left_i := (d + 1) / 2;
      assert 0 <= left_i <= d + 1;
      var left: nat := left_i;
      assert left <= d;
      var right: nat := d - left;
      assert right >= 0;
      result[i] := Spaces(left) + s + Spaces(right);
      assert |Spaces(left)| == left;
      assert |Spaces(right)| == right;
      assert |result[i]| == left + len + right;
      assert left + len + right == d + len;
      assert d + len == width;
      MiddleSlice(Spaces(left), s, Spaces(right));
      assert result[i] == Spaces(left) + s + Spaces(right);
      assert result[i][left .. left + len] == s;
      assert left == (width - len + 1) / 2;
    }
    i := i + 1;
  }
}
// </vc-code>
