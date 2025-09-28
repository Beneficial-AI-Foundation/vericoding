// <vc-preamble>

function count_upper(s: string): int
{
    if |s| == 0 then 0
    else (if 'A' <= s[0] <= 'Z' then 1 else 0) + count_upper(s[1..])
}

function count_lower(s: string): int
{
    if |s| == 0 then 0
    else (if 'a' <= s[0] <= 'z' then 1 else 0) + count_lower(s[1..])
}

function strength(s: string): int
{
    count_upper(s) - count_lower(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): rewrote as an iterative method to fix syntax and aid verification */
method FindStrongestIndex(exts: seq<string>) returns (result: int)
  requires |exts| > 0
  ensures 0 <= result < |exts|
  ensures forall j :: 0 <= j < |exts| ==> strength(exts[result]) >= strength(exts[j])
  ensures forall j :: 0 <= j < result ==> strength(exts[j]) < strength(exts[result])
{
  result := 0;
  var i := 1;
  while i < |exts|
    invariant 1 <= i <= |exts|
    invariant 0 <= result < i
    invariant forall j :: 0 <= j < i ==> strength(exts[result]) >= strength(exts[j])
    invariant forall j :: 0 <= j < result ==> strength(exts[j]) < strength(exts[result])
  {
    if strength(exts[i]) > strength(exts[result]) {
      result := i;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Strongest_Extension(class_name: string, extensions: seq<string>) returns (result: string)
    requires |extensions| > 0
    ensures exists i :: (0 <= i < |extensions| && result == class_name + "." + extensions[i] &&
            (forall j :: 0 <= j < |extensions| ==> strength(extensions[i]) >= strength(extensions[j])) &&
            (forall j :: 0 <= j < i ==> strength(extensions[j]) < strength(extensions[i])))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call helper to find index and construct result string */
  var i := FindStrongestIndex(extensions);
  result := class_name + "." + extensions[i];
}
// </vc-code>
