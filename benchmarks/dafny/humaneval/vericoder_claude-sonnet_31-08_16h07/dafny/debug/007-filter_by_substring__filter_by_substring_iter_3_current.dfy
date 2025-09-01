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
        var hasSubstring: bool;
        if |substring| == 0 {
            hasSubstring := true;
        } else if |strings[i]| < |substring| {
            hasSubstring := false;
        } else {
            hasSubstring := false;
            var j := 0;
            while j <= |strings[i]| - |substring|
                invariant 0 <= j <= |strings[i]| - |substring| + 1
            {
                var matches := true;
                var k := 0;
                while k < |substring| && matches
                    invariant 0 <= k <= |substring|
                    invariant matches ==> forall l :: 0 <= l < k ==> strings[i][j + l] == substring[l]
                {
                    if strings[i][j + k] != substring[k] {
                        matches := false;
                    }
                    k := k + 1;
                }
                if matches {
                    hasSubstring := true;
                    break;
                }
                j := j + 1;
            }
        }
        
        if hasSubstring {
            res := res + [strings[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

