method checkSubstring(s: string, sub: string) returns (result: bool)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma FilterPreservesElements(strings: seq<string>, substring: string, res: seq<string>)
    requires forall s :: s in res ==> (s in strings && checkSubstring(s, substring))
    ensures forall s :: s in res ==> s in strings
{
}

lemma FilterReducesSize(strings: seq<string>, res: seq<string>)
    requires forall s :: s in res ==> s in strings
    ensures |res| <= |strings|
{
    if |res| == 0 {
        return;
    }
    
    var count := 0;
    for i := 0 to |strings|
        invariant 0 <= count <= i
        invariant count >= |set s | s in res && s in strings[..i]|
    {
        if strings[i] in res {
            count := count + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    res := [];
    var i := 0;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant |res| <= i
        invariant forall s :: s in res ==> s in strings
    {
        if checkSubstring(strings[i], substring) {
            res := res + [strings[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

