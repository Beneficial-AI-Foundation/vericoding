predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
lemma {:induction false} LemmaAllDifferentUpTo<T(>)(s: seq<T>, i: int)
  requires 0 <= i <= |s|
  ensures forall k, j :: 0 <= j < k < i ==> s[j] != s[k]
  decreases i
{
  if i > 0 {
    LemmaAllDifferentUpTo(s, i - 1);
  }
}

lemma LemmaExistsDuplicate<T(>)(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures (exists j :: 0 <= j < i && s[j] == s[i]) ==> !forall k :: 0 <= k < i ==> s[k] != s[i]
  ensures !(exists j :: 0 <= j < i && s[j] == s[i]) ==> forall k :: 0 <= k < i ==> s[k] != s[i]
{
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
  output := [];
  var seen: set<string> := {};

  var i := 0;
  while i < |names|
    invariant 0 <= i <= |names|
    invariant |output| == i
    invariant forall k :: 0 <= k < i ==> 
        output[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
    invariant seen == set n | 0 <= k < i :: names[k]
    decreases |names| - i
  {
    if exists j :: 0 <= j < i && names[j] == names[i] {
      output := output + ["YES"];
    } else {
      output := output + ["NO"];
    }
    seen := seen + {names[i]};
    i := i + 1;
  }
}
// </vc-code>

