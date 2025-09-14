

// <vc-helpers>
lemma LemmaAboutExistence(s: seq<int>, Element: nat)
    requires |s| != 0
    ensures (exists i :: 0 <= i < |s| && s[i] == Element) || (forall i :: 0 <= i < |s| ==> s[i] != Element)
{
    if |s| == 1 {
        if s[0] == Element {
            assert exists i :: 0 <= i < |s| && s[i] == Element;
        } else {
            assert forall i :: 0 <= i < |s| ==> s[i] != Element;
        }
    } else {
        if s[0] == Element {
            assert exists i :: 0 <= i < |s| && s[i] == Element;
        } else {
            LemmaAboutExistence(s[1..], Element);
            if exists i :: 0 <= i < |s|-1 && s[1..][i] == Element {
                var i : int :| 0 <= i < |s|-1 && s[1..][i] == Element;
                assert s[i+1] == Element;
                assert exists j :: 0 <= j < |s| && s[j] == Element;
            } else {
                assert forall i :: 0 <= i < |s|-1 ==> s[1..][i] != Element;
                assert forall i :: 1 <= i < |s| ==> s[i] != Element;
                assert forall i :: 0 <= i < |s| ==> s[i] != Element;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
        requires n1 == |s1| && 0 <= n1 <= a.Length
        requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
        ensures Position == -1 || Position >= 1
        ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
// </vc-spec>
// <vc-code>
{
    if n1 == 0 {
        Position := -1;
        Count := 0;
    } else {
        LemmaAboutExistence(s1, Element);
        var found := false;
        var pos := -1;
        var cnt := 0;
        
        for i := 0 to n1
            invariant 0 <= i <= n1
            invariant pos == -1 <==> !found
            invariant pos == -1 || pos >= 1
            invariant pos >= 1 ==> found && 0 <= pos-1 < i && s1[pos-1] == Element
            invariant cnt == (if found then 1 else 0)
        {
            if a[i] == Element {
                if !found {
                    found := true;
                    pos := i + 1;
                    cnt := 1;
                }
            }
        }
        
        Position := pos;
        Count := cnt;
    }
}
// </vc-code>

