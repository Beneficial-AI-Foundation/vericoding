predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
lemma {:induction false} LemmaAllDifferentUpTo<T(==)>(s: seq<T>, i: int)
  requires 0 <= i <= |s|
  ensures forall k, j :: 0 <= j < k < i ==> s[j] != s[k]
  decreases i
{
  if i > 0 {
    LemmaAllDifferentUpTo(s, i - 1);
  }
}

lemma LemmaExistsDuplicate<T(==)>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures (exists j :: 0 <= j < i && s[j] == s[i]) ==> !forall k :: 0 <= k < i ==> s[k] != s[i]
  ensures !(exists j :: 0 <= j < i && s[j] == s[i]) ==> forall k :: 0 <= k < i ==> s[k] != s[i]
{
  if exists j :: 0 <= j < i && s[j] == s[i] {
    // Trivially, if there exists a duplicate, then not all elements are different
  } else {
    // No duplicates exist
  }
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
  output := [];
  var i := 0;
  while i < |names|
    invariant 0 <= i <= |names|
    invariant |output| == i
    invariant forall k :: 0 <= k < i ==> 
        output[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
    decreases |names| - i
  {
    var found := false;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant found == (exists k :: 0 <= k < j && names[k] == names[i])
      decreases i - j
    {
      if names[j] == names[i] {
        found := true;
        j := i; // break
      } else {
        j := j + 1;
      }
    }
    
    if found {
      output := output + ["YES"];
    } else {
      output := output + ["NO"];
    }
    i := i + 1;
  }
}
// </vc-code>

