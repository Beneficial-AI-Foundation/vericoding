predicate isSubstring(sub: seq<char>, str: seq<char>)
{
    exists i :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

// We spent 2h each on this assignment

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
    //ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  assume{:axiom} false;
}

// <vc-helpers>
function haveCommonKSubstringHolds(k: nat, str1: string, str2: string): (bool)
  ensures haveCommonKSubstringHolds(k, str1, str2) <==> haveCommonKSubstringPred(k, str1, str2)
{
  exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

lemma IsSubstringPredImpliesHasPrefix(sub:string, str:string, i:nat)
  requires |sub| <= |str| - i && sub == str[i..i+|sub|]
  ensures isSubstringPred(sub, str)
{
}

lemma haveCommonKSubstringPredRefinement(k: nat, str1: string, str2: string)
  ensures haveCommonKSubstringPred(k, str1, str2) <==> (exists i1 :: 0 <= i1 && i1 + k <= |str1| && exists i2 :: 0 <= i2 && i2 + k <= |str2| && str1[i1..i1+k] == str2[i2..i2+k])
{
  if haveCommonKSubstringPred(k, str1, str2) {
    // If haveCommonKSubstringPred(k, str1, str2) is true, then by definition:
    // exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
    // Let's pick such i1, j1.
    // Let sub := str1[i1..j1]. We know |sub| == k.
    // And isSubstringPred(sub, str2) means:
    // exists i_sub :: 0 <= i_sub <= |str2| && isPrefixPred(sub, str2[i_sub..])
    // Which means:
    // exists i_sub :: 0 <= i_sub <= |str2| && |sub| <= |str2[i_sub..]| && sub == str2[i_sub..i_sub+|sub|]
    // Since |sub| == k, we have:
    // exists i_sub :: 0 <= i_sub <= |str2| - k && str1[i1..i1+k] == str2[i_sub..i_sub+k]
    // So we found such i1 and i2 (i_sub).
    var i1_witness, j1_witness : nat;
    var i2_witness : nat;
    ghost if (exists i1', j1' :: 0 <= i1' <= |str1|- k && j1' == i1' + k && isSubstringPred(str1[i1'..j1'],str2)) {
        i1_witness := (i1' witness);
        j1_witness := (j1' witness);
        var sub_witness := str1[i1_witness..j1_witness];
        IsSubstringPredImpliesHasPrefix(sub_witness, str2, i2_witness);
        assert (0 <= i1_witness && i1_witness + k <= |str1| && 0 <= i2_witness && i2_witness + k <= |str2| && str1[i1_witness..i1_witness+k] == str2[i2_witness..i2_witness+k]);
    }
    assert (exists i1 :: 0 <= i1 && i1 + k <= |str1| && exists i2 :: 0 <= i2 && i2 + k <= |str2| && str1[i1..i1+k] == str2[i2..i2+k]);

  } else {
    // If haveCommonKSubstringPred(k, str1, str2) is false, then by definition:
    // forall i1, j1 :: not (0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2))
    // Which means:
    // forall i1 :: 0 <= i1 <= |str1|- k ==> not isSubstringPred(str1[i1..i1+k],str2)
    // not isSubstringPred(sub, str2) means:
    // forall i_sub :: not (0 <= i_sub <= |str2| && isPrefixPred(sub, str2[i_sub..]))
    // Which means:
    // forall i_sub :: not (0 <= i_sub <= |str2| - k && str1[i1..i1+k] == str2[i_sub..i_sub+k])
    // So, forall i1 :: 0 <= i1 <= |str1|- k ==> (forall i2 :: not (0 <= i2 <= |str2|-k && str1[i1..i1+k] == str2[i2..i2+k]))
    // This is equivalent to:
    // forall i1, i2 :: not (0 <= i1 <= |str1|-k && 0 <= i2 <= |str2|-k && str1[i1..i1+k] == str2[i2..i2+k])
    // Which is equivalent to:
    // not (exists i1, i2 :: 0 <= i1 <= |str1|-k && 0 <= i2 <= |str2|-k && str1[i1..i1+k] == str2[i2..i2+k])
    assert (! (exists i1 :: 0 <= i1 && i1 + k <= |str1| && exists i2 :: 0 <= i2 && i2 + k <= |str2| && str1[i1..i1+k] == str2[i2..i2+k]));
  }
}

function computeHaveCommonKSubstring(k: nat, str1: string, str2: string): bool
  requires k >= 0
  ensures computeHaveCommonKSubstring(k, str1, str2) <==> haveCommonKSubstringPred(k, str1, str2)
{
  if k == 0 then true // Any two strings have an empty common substring if k=0
  else if k > |str1| || k > |str2| then false
  else
    (exists i1 :: 0 <= i1 && i1 + k <= |str1| &&
    (exists i2 :: 0 <= i2 && i2 + k <= |str2| &&
      str1[i1 .. i1 + k] == str2[i2 .. i2 + k]))
}
// </vc-helpers>

// <vc-spec>
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires (|str1| <= |str2|)
    ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    ensures haveCommonKSubstringPred(len,str1,str2)
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := |str1|;
    var currentMaxLen := 0;

    // A common substring of length 0 always exists.
    // If |str1| is 0, then the maximum common substring length is 0.
    if (|str1| == 0) {
        return 0;
    }

    while low <= high
        invariant 0 <= low <= |str1| + 1 // low can go up to |str1|+1
        invariant -1 <= high <= |str1| // high can go down to -1
        invariant 0 <= currentMaxLen <= |str1|
        invariant currentMaxLen <= low
        invariant haveCommonKSubstringPred(currentMaxLen, str1, str2)
        invariant (forall k_prime :: high < k_prime <= |str1| ==> !haveCommonKSubstringPred(k_prime, str1, str2))
        decreases high - low
    {
        var mid := (low + high) / 2;

        if mid > |str1| { mid := |str1|; }
        if mid < 0 { mid := 0; }

        if mid == 0 {
            currentMaxLen := 0;
            low := 1;
            // haveCommonKSubstringPred(0, str1, str2) is always true.
            // haveCommonKSubstringPred(0, str1, str2)
            // == (exists i1, j1 :: 0 <= i1 <= |str1|- 0 && j1 == i1 + 0 && isSubstringPred(str1[i1..j1],str2))
            // == (exists i1 :: 0 <= i1 <= |str1| && isSubstringPred("",str2))
            // isSubstringPred("",str2) == (exists i :: 0 <= i <= |str2| && isPrefixPred("", str2[i..]))
            // isPrefixPred("", str2[i..]) == (|""| <= |str2[i..]|) && "" == str2[i..|""|] == ("" <= |str2|-i && "" == "")
            // This is trivially true for any i. So, this holds.
            continue;
        }

        // We need to ensure that mid is a valid substring length to query.
        // mid must be <= |str1| and <= |str2|. This is implied by mid <= high <= |str1| and the initial |str1| <= |str2| requirement.
        if computeHaveCommonKSubstring(mid, str1, str2) {
            currentMaxLen := mid;
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    len := currentMaxLen;

    // After the loop, low > high.
    // We want to prove:
    // 1. haveCommonKSubstringPred(len, str1, str2)
    //    This follows directly from the loop invariant: haveCommonKSubstringPred(currentMaxLen, str1, str2)
    // 2. (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
    //    From the loop invariant: (forall k_prime :: high < k_prime <= |str1| ==> !haveCommonKSubstringPred(k_prime, str1, str2))
    //    We need to show that len == high (or something similar).
    //    Consider the state when the loop terminates:
    //    If the last `computeHaveCommonKSubstring(mid, str1, str2)` was true, then currentMaxLen = mid, low = mid + 1. high remains unchanged.
    //    The loop terminates because low became greater than high.
    //    So, (mid_last_true + 1) > high_last_true.
    //    The values of `currentMaxLen` and `high` at termination are such that: `currentMaxLen` is the largest `mid` for which `computeHaveCommonKSubstring` returned true. `high` points to the last `mid` for which `computeHaveCommonKSubstring` returned false.
    //    After the loop, currentMaxLen is the length of the longest common substring found so far.
    //    And high is either currentMaxLen or currentMaxLen - 1 (if no substring found).
    //    If computeHaveCommonKSubstring(mid, str1, str2) returns true, we set `low = mid + 1`. This makes `currentMaxLen = mid`.
    //    If computeHaveCommonKSubstring(mid, str1, str2) returns false, we set `high = mid - 1`.
    //    When the loop terminates, `low` will be `currentMaxLen + 1` and `high` will be `currentMaxLen` if a common substring exists.
    //    If no common substring exists, `currentMaxLen` will be 0, `high` will be -1, and low will be 1.
    //    In the case where some `currentMaxLen` > 0 is found:
    //    `low` ends up pointing to `currentMaxLen + 1`. `high` ends up pointing to `currentMaxLen`.
    //    So, `len == high`.
    //    Therefore, `(forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))` is true.
    //    This is because any `k_prime` for which `high < k_prime` means `len < k_prime`.
}
// </vc-code>

