// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed start_pos calculation to match postcondition */
function PadLeft(s: string, count: int): string
  requires count >= 0
  ensures |PadLeft(s, count)| == |s| + count
  ensures forall j :: 0 <= j < count ==> PadLeft(s, count)[j] == ' '
  ensures forall j :: count <= j < |PadLeft(s, count)| ==> PadLeft(s, count)[j] == s[j - count]
  decreases count
{
  if count <= 0 then
    s
  else
    " " + PadLeft(s, count - 1)
}

function PadRight(s: string, count: int): string
  requires count >= 0
  ensures |PadRight(s, count)| == |s| + count
  ensures forall j :: 0 <= j < |s| ==> PadRight(s, count)[j] == s[j]
  ensures forall j :: |s| <= j < |PadRight(s, count)| ==> PadRight(s, count)[j] == ' '
  decreases count
{
  if count <= 0 then
    s
  else
    PadRight(s + " ", count - 1)
}

function max(a: int, b: int): int {
  if a > b then a else b
}

lemma PadLeftPadRightProperty(s: string, padLeft: int, padRight: int)
  requires padLeft >= 0 && padRight >= 0
  ensures |PadLeft(s, padLeft) + PadRight("", padRight)| == |s| + padLeft + padRight
  ensures forall j :: padLeft <= j < padLeft + |s| ==> (PadLeft(s, padLeft) + PadRight("", padRight))[j] == s[j - padLeft]
{
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
/* code modified by LLM (iteration 4): Fixed start_pos calculation to use (width - |input[i]| + 1)/2 */
{
  result := new string[input.Length];
  
  var i := 0;
  while i < input.Length
    invariant 0 <= i <= input.Length
    invariant forall j :: 0 <= j < i ==> |result[j]| == max(|input[j]|, width)
    invariant forall j :: 0 <= j < i ==> 
      if |input[j]| < width then
        var start_pos := (width - |input[j]| + 1) / 2;
        result[j][start_pos..start_pos + |input[j]|] == input[j]
      else true
  {
    var s := input[i];
    if |s| >= width {
      result[i] := s;
    } else {
      var totalPadding := width - |s|;
      var padLeft := (totalPadding + 1) / 2;
      var padRight := totalPadding - padLeft;
      var leftPadded := PadLeft(s, padLeft);
      result[i] := leftPadded + PadRight("", padRight);
    }
    i := i + 1;
  }
}
// </vc-code>
