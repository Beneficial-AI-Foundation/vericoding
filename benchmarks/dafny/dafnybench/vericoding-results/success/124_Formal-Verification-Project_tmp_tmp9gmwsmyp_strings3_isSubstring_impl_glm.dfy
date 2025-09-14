predicate isPrefixPred(pre:string, str:string)
{
    (|pre| <= |str|) && 
    pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
}
predicate isSubstringPred(sub:string, str:string)
{
    (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
    (forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

// <vc-helpers>
lemma isPrefixIff(pre: string, str: string)
    ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
{
    calc {
        isPrefixPred(pre, str) <==>
        (|pre| <= |str|) && pre == str[..|pre|] <==>
        !((|pre| > |str|) || pre != str[..|pre|]) <==>
        !isNotPrefixPred(pre, str);
    }
}

lemma isSubstringIff(sub: string, str: string)
    ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
{
    calc {
        isSubstringPred(sub, str) <==>
        exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..]) <==>
        exists i :: 0 <= i <= |str| && !isNotPrefixPred(sub, str[i..]) <==>
        !(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..])) <==>
        !isNotSubstringPred(sub, str);
    }
}

lemma DecomposeSubstring(sub: string, str: string)
    requires |str| > 0
    ensures isSubstringPred(sub, str) <==> (isPrefixPred(sub, str) || isSubstringPred(sub, str[1..]))
{
    if isSubstringPred(sub, str) {
        var i :| 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
        if i == 0 {
            assert isPrefixPred(sub, str);
        } else {
            assert i >= 1;
            assert i <= |str|;
            assert |str[1..]| == |str| - 1;
            assert 0 <= i-1 <= |str[1..]|;
            assert str[1..][i-1..] == str[i..];
            assert isPrefixPred(sub, str[1..][i-1..]);
            assert isSubstringPred(sub, str[1..]);
        }
    }
    if isPrefixPred(sub, str) {
        assert isPrefixPred(sub, str[0..]);
        assert 0<=0<=|str|;
        assert isSubstringPred(sub, str);
    }
    if isSubstringPred(sub, str[1..]) {
        var j :| 0 <= j <= |str[1..]| && isPrefixPred(sub, str[1..][j..]);
        assert 0 <= j <= |str[1..]|;
        assert |str[1..]| == |str| - 1;
        assert j+1 >= 1;
        assert j+1 <= |str|;
        assert str[j+1..] == str[1..][j..];
        assert isPrefixPred(sub, str[j+1..]);
        assert isSubstringPred(sub, str);
    }
}
// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
    //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    if |sub| == 0 {
        assert isPrefixPred("", str[0..]);
        assert 0<=0<=|str|;
        assert isSubstringPred("", str);
        return true;
    }
    if |str| == 0 {
        assert |sub| > 0;
        assert forall i: int :: 0<=i<=0 ==> isNotPrefixPred(sub, ""[i..]) by {
            forall i: int | 0<=i<=0 ensures isNotPrefixPred(sub, ""[i..]) {
                assert i==0;
                assert ""[i..] == "";
                assert |sub| > 0;
                assert |sub| > |""|;
                assert isNotPrefixPred(sub, "");
            }
        }
        assert isNotSubstringPred(sub, "");
        assert !isSubstringPred(sub, "");
        return false;
    }
    DecomposeSubstring(sub, str);
    if isPrefixPred(sub, str) {
        assert isPrefixPred(sub, str[0..]);
        assert 0<=0<=|str|;
        assert isSubstringPred(sub, str);
        return true;
    } else {
        var rec := isSubstring(sub, str[1..]);
        assert isSubstringPred(sub, str) <==> isSubstringPred(sub, str[1..]);
        assert rec <==> isSubstringPred(sub, str[1..]);
        assert rec <==> isSubstringPred(sub, str);
        return rec;
    }
}
// </vc-code>

