//IMPL 
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
    if |s| <= 1 {
        result := true;
    } else {
        var i := 1;
        result := true;
        /* code modified by LLM (iteration 1): enhanced loop invariant to properly track the relationship between result and characters checked */
        while i < |s| && result
            invariant 1 <= i <= |s|
            invariant result ==> forall k :: 0 <= k < i ==> s[k] == s[0]
            invariant !result ==> exists k :: 0 <= k < i && s[k] != s[0]
        {
            if s[i] != s[0] {
                result := false;
            }
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 1): added assertions to help Dafny verify the postconditions */
        if result {
            // All characters from 0 to |s|-1 are the same as s[0]
            assert forall k :: 0 <= k < |s| ==> s[k] == s[0];
            assert forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j];
        } else {
            // We found at least one character different from s[0]
            assert exists k :: 0 <= k < |s| && s[k] != s[0];
            assert |s| > 1;
            assert exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j];
        }
    }
}