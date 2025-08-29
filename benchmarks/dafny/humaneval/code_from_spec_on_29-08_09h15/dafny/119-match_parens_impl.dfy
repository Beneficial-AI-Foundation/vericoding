function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma CalcBalProperties(s: seq<int>, i: int, j: int, acc: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: 0 <= k < |s| ==> s[k] == 0 || s[k] == 1
    ensures CalcBal(s, i, j, acc) == acc + CalcBal(s, i, j, 0)
{
    if i == j {
    } else {
        CalcBalProperties(s, i, j - 1, acc);
    }
}

lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int, acc: int)
    requires 0 <= i <= j <= k <= |s|
    requires forall m :: 0 <= m < |s| ==> s[m] == 0 || s[m] == 1
    ensures CalcBal(s, i, k, acc) == CalcBal(s, j, k, CalcBal(s, i, j, acc))
{
    if j == k {
    } else {
        CalcBalMonotonic(s, i, j, k - 1, acc);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def match_parens(l : list[str]) -> str
You are given a list of two strings, both strings consist of open parentheses '(' or close parentheses ')' only. Your job is to check if it is possible to concatenate the two strings in some order, that the resulting string will be good. A string S is considered to be good if and only if all parentheses in S are balanced. For example: the string '(())()' is good, while the string '())' is not. Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
*/
// </vc-description>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 
    // pre-conditions-start
    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    var valid1 := true;
    var i := 0;
    while i <= |s1| && valid1
        invariant 0 <= i <= |s1| + 1
        invariant valid1 ==> forall j :: 0 <= j < i ==> CalcBal(s1, 0, j, 0) >= 0
        invariant !valid1 ==> exists j :: 0 <= j < i && CalcBal(s1, 0, j, 0) < 0
    {
        if CalcBal(s1, 0, i, 0) < 0 {
            valid1 := false;
        }
        i := i + 1;
    }
    
    if !valid1 {
        b := false;
        return;
    }
    
    var bal1 := CalcBal(s1, 0, |s1|, 0);
    var valid2 := true;
    i := 0;
    while i <= |s2| && valid2
        invariant 0 <= i <= |s2| + 1
        invariant valid2 ==> forall j :: 0 <= j < i ==> bal1 + CalcBal(s2, 0, j, 0) >= 0
        invariant !valid2 ==> exists j :: 0 <= j < i && bal1 + CalcBal(s2, 0, j, 0) < 0
    {
        if bal1 + CalcBal(s2, 0, i, 0) < 0 {
            valid2 := false;
        }
        i := i + 1;
    }
    
    b := valid1 && valid2;
}
// </vc-code>

