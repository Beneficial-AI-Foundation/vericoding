predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


//ATOM

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}


//ATOM

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1],str2)
}


//ATOM
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  /* code modified by LLM (iteration 1): Fixed logic to correctly establish postcondition */
  res := false;
  
  var i := 0;
  while i <= |str| && !res
    invariant 0 <= i <= |str| + 1
    invariant res ==> isSubstringPred(sub, str)
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
  {
    if isPrefixPred(sub, str[i..]) {
      res := true;
      /* code modified by LLM (iteration 1): Added witness for existential */
      assert isSubstringPred(sub, str) by {
        assert 0 <= i <= |str| && isPrefixPred(sub, str[i..]);
      }
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added final proof for !res case */
  if !res {
    assert !isSubstringPred(sub, str) by {
      assert forall j :: 0 <= j <= |str| ==> !isPrefixPred(sub, str[j..]);
    }
  }
  
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): Removed assume statements and implemented basic logic */
  if |pre| > |str| {
    res := false;
  } else {
    res := (pre == str[..|pre|]);
  }
  return res;
}


//ATOM

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	
	if |str1| < k {
		/* code modified by LLM (iteration 1): Added explicit reasoning for empty case */
		// When |str1| < k, no k-length substring exists, so haveCommonKSubstringPred is false
		assert !haveCommonKSubstringPred(k, str1, str2);
		return;
	}
	
	var i := 0;
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		/* code modified by LLM (iteration 1): Fixed invariant with explicit trigger */
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
		invariant !found ==> (forall i1 :: 0 <= i1 < i && i1 + k <= |str1| ==> !isSubstringPred(str1[i1..i1+k], str2)) {:trigger str1[i1..i1+k]}
	{
		var substring := str1[i..i+k];
		var isSubstr := isSubstring(substring, str2);
		
		if isSubstr {
			found := true;
			/* code modified by LLM (iteration 1): Added witness for existential */
			// At this point, we have found a common k-substring at position i
			assert isSubstringPred(str1[i..i+k], str2);
			assert haveCommonKSubstringPred(k, str1, str2) by {
				// Witness: i1 = i, j1 = i + k
				assert 0 <= i <= |str1| - k && (i + k) == i + k && isSubstringPred(str1[i..i+k], str2);
			}
			return;
		}
		
		/* code modified by LLM (iteration 1): Added assertion to maintain invariant */
		assert !isSubstringPred(str1[i..i+k], str2);
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): Fixed final proof with correct reasoning */
	// Loop has ended and found is still false
	// We need to prove !haveCommonKSubstringPred(k, str1, str2)
	assert !haveCommonKSubstringPred(k, str1, str2) by {
		// From the loop invariant, we checked all positions 0 <= i1 < (|str1| - k + 1)
		// Since found is false and the loop covered all valid positions
		assert forall i1 :: 0 <= i1 <= |str1|- k ==> !isSubstringPred(str1[i1..i1+k], str2);
		// This contradicts the existence claimed by haveCommonKSubstringPred
	}
}