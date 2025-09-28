// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [code is correct; updating comment for new iteration] */
function BuildPadding(n: nat, c: char): (res: string)
    ensures |res| == n
    ensures forall i :: 0 <= i < n ==> res[i] == c
    decreases n
{
    if n == 0 then "" else [c] + BuildPadding(n-1, c)
}

/* helper modified by LLM (iteration 4): [code is correct; updating comment for new iteration] */
function RJustString(s: string, width: nat, fillchar: string): (r: string)
    requires |fillchar| == 1
    ensures |r| == (if |s| >= width then |s| else width)
    ensures |s| >= width ==> r == s
    ensures |s| < width ==> 
        |r| == width &&
        (forall j :: 0 <= j < |s| ==> r[width - |s| + j] == s[j]) &&
        (forall j :: 0 <= j < width - |s| ==> r[j] == fillchar[0])
{
    if |s| >= width then s else BuildPadding(width - |s|, fillchar[0]) + s
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
  /* code modified by LLM (iteration 4): [replace seq comprehension with while loop to fix compilation error] */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
        |result[k]| == (if |a[k]| >= width then |a[k]| else width) &&
        (|a[k]| >= width ==> result[k] == a[k]) &&
        (|a[k]| < width ==> 
            |result[k]| == width &&
            (forall j :: 0 <= j < |a[k]| ==> result[k][width - |a[k]| + j] == a[k][j]) &&
            (forall j :: 0 <= j < width - |a[k]| ==> result[k][j] == fillchar[0]))
  {
    var r := RJustString(a[i], width, fillchar);
    result := result + [r];
    i := i + 1;
  }
}
// </vc-code>
