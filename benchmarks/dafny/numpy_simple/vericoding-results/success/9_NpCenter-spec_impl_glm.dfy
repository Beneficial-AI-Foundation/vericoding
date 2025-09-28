// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed centering alignment and replaced PadLeft with sequence comprehension */
function PadString(s: string, width: int): string
  ensures |PadString(s, width)| == (if |s| > width then |s| else width)
  ensures |s| < width ==> var start_pos := (width - |s| + 1) / 2; PadString(s, width)[start_pos..start_pos + |s|] == s
{
  if |s| > width then s else
    var d := width - |s|;
    var left := (d + 1) / 2;
    var right := d - left;
    seq(left, i => ' ') + s + seq(right, i => ' ')
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
  /* code modified by LLM (iteration 2): implemented centering using PadString helper */
  result := new string[input.Length];
  for i := 0 to input.Length
    invariant 0 <= i <= input.Length
    invariant forall j :: 0 <= j < i ==> result[j] == PadString(input[j], width)
  {
    if i < input.Length {
      result[i] := PadString(input[i], width);
    }
  }
}
// </vc-code>
