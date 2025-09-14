predicate isSubstring(sub: string, str: string)
{
    exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

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

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
}

// <vc-helpers>
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found <==> haveCommonKSubstringPred(k, str1, str2)
    ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
    found := false;
    if k == 0 {
        return true;
    }
    if k > |str1| || k > |str2| {
        return false;
    }
    var i1 := 0;
    while i1 <= |str1| - k
        invariant 0 <= i1 <= |str1| - k + 1
        invariant found <==> exists m :: 0 <= m < i1 && (exists n :: 0 <= n <= |str2| - k && str1[m..m + k] == str2[n..n + k])
    {
        var sub := str1[i1..i1 + k];
        var isIn := false;
        var i2 := 0;
        while i2 <= |str2| - k
            invariant 0 <= i2 <= |str2| - k + 1
            invariant isIn <==> exists n :: 0 <= n < i2 && sub == str2[n..n + k]
        {
            if sub == str2[i2..i2 + k] {
                isIn := true;
            }
            i2 := i2 + 1;
        }
        if isIn {
            found := true;
        }
        i1 := i1 + 1;
    }
    return found;
}
// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
:
  var low : nat := 0;
  var high : nat := |str1| ;
  while low + 1 < high
     invariant 0 <= low <= high <= |str1|
     invariant forall k :: high < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
     invariant haveCommonKSubstringPred(low, str1, str2)
  {
    var mid := (low + high + 1) / 2;
    if haveCommonKSubstring(mid, str1, str2) {
      low := mid;
    } else {
      high := mid - 1;
    }
  }
  len := low;
// </vc-code>

