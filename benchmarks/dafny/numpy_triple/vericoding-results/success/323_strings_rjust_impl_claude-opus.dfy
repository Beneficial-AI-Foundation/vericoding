// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RJustString(s: string, width: nat, fillchar: string): string
  requires |fillchar| == 1
  ensures |s| >= width ==> RJustString(s, width, fillchar) == s
  ensures |s| < width ==> |RJustString(s, width, fillchar)| == width
  ensures |s| < width ==> forall j :: 0 <= j < width - |s| ==> RJustString(s, width, fillchar)[j] == fillchar[0]
  ensures |s| < width ==> forall j :: 0 <= j < |s| ==> RJustString(s, width, fillchar)[width - |s| + j] == s[j]
{
  if |s| >= width then
    s
  else
    seq(width - |s|, i => fillchar[0]) + s
}
// </vc-helpers>

// <vc-spec>
method RJust(a: seq<string>, width: nat, fillchar: string) returns (result: seq<string>)
    requires |fillchar| == 1
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> 
        // Length invariant: result length is exactly max(orig.length, width)
        |result[i]| == (if |a[i]| >= width then |a[i]| else width) &&
        // Identity morphism: strings already >= width are unchanged
        (|a[i]| >= width ==> result[i] == a[i]) &&
        // Right-justification: when padding needed, original appears as suffix
        (|a[i]| < width ==> 
            |result[i]| == width &&
            // Original string is preserved as suffix
            (forall j :: 0 <= j < |a[i]| ==> result[i][width - |a[i]| + j] == a[i][j]) &&
            // Padding characters are fillchar
            (forall j :: 0 <= j < width - |a[i]| ==> result[i][j] == fillchar[0])) &&
        // Minimality constraint: no over-padding when not needed
        (|a[i]| >= width ==> |result[i]| == |a[i]|) &&
        // Exactness constraint: padding achieves exact width requirement  
        (|a[i]| < width ==> |result[i]| == width) &&
        // Consistency constraint: empty strings padded to full width
        (|a[i]| == 0 ==> |result[i]| == width)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == (if |a[k]| >= width then |a[k]| else width)
    invariant forall k :: 0 <= k < i ==> |a[k]| >= width ==> result[k] == a[k]
    invariant forall k :: 0 <= k < i ==> |a[k]| < width ==> |result[k]| == width
    invariant forall k :: 0 <= k < i ==> |a[k]| < width ==> forall j :: 0 <= j < |a[k]| ==> result[k][width - |a[k]| + j] == a[k][j]
    invariant forall k :: 0 <= k < i ==> |a[k]| < width ==> forall j :: 0 <= j < width - |a[k]| ==> result[k][j] == fillchar[0]
  {
    var padded := RJustString(a[i], width, fillchar);
    result := result + [padded];
    i := i + 1;
  }
}
// </vc-code>
